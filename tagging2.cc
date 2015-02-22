//構文解析を援用した、WSJコーパスを学習・評価に用いた品詞タグ(POSタグ)付け
//構文解析用の学習データ(train.conll/CoNLL08SharedTaskのデータ)及び
//学習用データ(wsj00-18.pos)とテスト用データ(wsj19-21.pos)を同じフォルダに置いて実行する
#include<vector>
#include<cmath>
#include<map>
#include<cstdlib>
#include<iostream>
#include<sstream>
#include<fstream>
#include<string>
#include<algorithm>
#include<cstring>
#include<cstdio>
#include<set>
#include<stack>
#include<bitset>
#include<functional>
#include<ctime>
#include<queue>
#include<deque>
#include<complex>
using namespace std;
#define pb push_back
#define pf push_front
typedef long long lint;
typedef complex<double> P;
#define mp make_pair
#define fi first
#define se second
typedef pair<int,double> pint;
typedef pair<double,pair<int,int> > tint;
typedef pair<double,int> pdou;
#define All(s) s.begin(),s.end()
#define rAll(s) s.rbegin(),s.rend()
#define REP(i,a,b) for(int i=a;i<b;i++)
#define rep(i,n) REP(i,0,n)
typedef double typ;
#define N 180000//特徴ベクトルの次元数
#define L 19100000//特徴ベクトルの次元数（構文解析）
#define M 45//品詞の種類
#define K 5//学習を繰り返す回数
#define O 5//学習を繰り返す回数（構文解析）
#define P 2//学習を繰り返す回数（Reranker）
#define W 10//ビーム幅
int o=0;//学習した単語の種類
double B=0.7;//タグのbi-gramの重み
double T=0.4;//タグのtri-gramの重み

//単語・タグと数字の変換用
map<string,int> de,de2;
vector <string> en,en2;

vector <string> go[2][40000];//単語そのもの
vector <int> po[2][40000],wo[2][40000],ro[2][40000];//タグ・単語・親ノードの数字

//tag用
vector <vector <pint> > v[2][40000];//各文ごとのフィーチャー
double wtag[M+2][N+2],w2tag[M+2][N+2];//タグ付けの重みベクトル
vector<int> pos[W+2];//タグ付けの結果
tint beam[300][M*W+2];//ビームサーチ用
double tagscore[W+2];//タグ付けのスコア

//parse用
vector<pint> fea[300][300];//フィーチャーベクトル
double wpar[L];//重みベクトル
double w2par[L];//平均化ベクトル
vector<int> tree;//構文木
double parscore[W+2];//タグ付けのスコア
typ inf=1e9,CONST=1e5;
map<pint,int> biword;

//reranker用
double alpha[L];//reranker用の重みベクトル
vector<int> feat[40000][W+2];
double score[40000][W+2],ls[40000][W+2];

vector<double> tags,pars;

//ここから構文解析用の関数
//フィーチャーベクトルを作る
void hen(vector<int> word,vector<int> postag){
	int n=word.size();
	rep(i,n+1) rep(j,n+1) fea[i][j].clear();
	rep(i,n){
		fea[0][i+1].pb(mp(postag[i],1.0));
		fea[0][i+1].pb(mp(word[i]+50,1.0));
		fea[0][i+1].pb(mp(50000+word[i]*46+postag[i],1.0));
	}
	rep(i,n) rep(j,n){
		if(i==j) continue;
		//p-pos
		fea[i+1][j+1].pb(mp(2200000+postag[i],0.5));
		//p-word
		fea[i+1][j+1].pb(mp(2200050+word[i],0.5));
		//p-pos,p-word
		fea[i+1][j+1].pb(mp(2250000+word[i]*46+postag[i],0.5));
		//c-pos
		fea[i+1][j+1].pb(mp(4400000+postag[j],1.0));
		//c-word
		fea[i+1][j+1].pb(mp(4400050+word[j],1.0));
		//c-pos,c-word
		fea[i+1][j+1].pb(mp(4450000+word[j]*46+postag[j],1.0));
		//p-pos,c-pos
		fea[i+1][j+1].pb(mp(6600000+46*postag[i]+postag[j],0.8));
		//p-word,c-pos
		fea[i+1][j+1].pb(mp(6603000+46*word[i]+postag[j],1.0));
		//p-pos,c-word
		fea[i+1][j+1].pb(mp(8753000+46*word[j]+postag[i],1.0));
		//p-pos,p-pos+1,c-pos
		if(i<n-1){
			fea[i+1][j+1].pb(mp(11000000+2116*postag[i]+46*postag[i+1]+postag[j],1.0));
		}
		//p-pos,p-pos-1,c-pos
		if(i>0){
			fea[i+1][j+1].pb(mp(11100000+2116*postag[i]+46*postag[i-1]+postag[j],1.0));
		}
		//p-pos,c-pos,c-pos+1
		if(j<n-1){
			fea[i+1][j+1].pb(mp(11200000+2116*postag[i]+46*postag[j]+postag[j+1],1.0));
		}
		//p-pos,c-pos,c-pos-1
		if(j>0){
			fea[i+1][j+1].pb(mp(11300000+2116*postag[i]+46*postag[j]+postag[j-1],1.0));
		}
		//p-word,c-word
		fea[i+1][j+1].pb(mp(12000000+biword[mp(word[i],word[j])],1.0));
		//p-pos,b-pos,c-pos
		REP(k,i+1,j){
			fea[i+1][j+1].pb(mp(19000000+2116*postag[i]+46*postag[j]+postag[k],1.0));
		}
	}
}
//DMSTライブラリ
vector<int> dmst(int root,int V,vector<vector<typ> > gr){
	vector<int> ret(V,-1),id(V,-1),vis(V,-1);
	rep(i,V) rep(j,V){
		if(i==root || i==j) continue;
		if(ret[i]<0){
			if(gr[j][i]<inf) ret[i]=j;
		}
		else if(gr[ret[i]][i]>gr[j][i]) ret[i]=j;
	}
	int t=0;
	rep(i,V){
		int v=i;
		while(vis[v]!=i && id[v]==-1 && v!=root){
			vis[v]=i;v=ret[v];
		}
		if(v!=root && id[v]==-1){
			for(int u=ret[v];u!=v;u=ret[u]) id[u]=t;id[v]=t++;
		}
	}
	if(t==0) return ret;
	rep(i,V){if(id[i]==-1) id[i]=t++;}
	vector<typ> tmp(t,inf);vector<vector<typ> > gr2(t,tmp);
	vector<int> tm2(t,-1);vector<vector<int> > from(t,tm2),to(t,tm2);
	rep(i,V) rep(j,V){
		if(id[i]==id[j] || gr[i][j]>=inf) continue;
		typ co=gr[i][j]-gr[ret[j]][j];
		int u=id[i],v=id[j];
		if(from[u][v]<0 || gr2[u][v]>co){
			from[u][v]=i;to[u][v]=j;gr2[u][v]=co;
		}
	}
	vector<int> nex=dmst(id[root],t,gr2);
	rep(i,t){
		if(nex[i]>=0) ret[to[nex[i]][i]]=from[nex[i]][i];
	}
	return ret;
}
//木を作ってパーズする
double parse(vector<int> word,vector<int> postag){
	int n=word.size();
	hen(word,postag);
	vector<typ> cl(n+1,inf);
	vector<vector<typ> > gr(n+1,cl);
	rep(i,n+1) REP(j,1,n+1){
		if(i==j) continue;
		double wei=0.0;
		rep(k,fea[i][j].size()) wei+=wpar[fea[i][j][k].fi]*fea[i][j][k].se;
		gr[i][j]=-wei;if(i<1) gr[i][j]+=CONST;
	}
	tree=dmst(0,n+1,gr);
	double ret=+CONST;
	REP(j,1,n+1) ret-=gr[tree[j]][j];
	return ret;
}
//ここまで

//ここからタグ付け用の関数
int dec(string a){
	int ret=0;
	rep(i,a.size()){
		ret*=27;
		if(a[i]=='^') ret+=26;
		else if(a[i]<='z' && a[i]>='a') ret+=(a[i]-'a');
		else if(a[i]<='Z' && a[i]>='A') ret+=(a[i]-'A');
		else ret+=26;
	}
	return ret;
}
void henkan(vector <string> word,int it,int it2){
	int ws=word.size();
	rep(i,ws){
		vector <pint> tmp;
		tmp.pb(mp(de[word[i]],1));
		if(i>0) tmp.pb(mp(de[word[i-1]]+50000,0.8));
		if(i<ws-1) tmp.pb(mp(de[word[i+1]]+100000,0.8));
		string s="^"+word[i]+"^";int l=s.size();
		rep(j,l-1) tmp.pb(mp(dec(s.substr(j,2))+150000,0.3));
		rep(j,l-2) tmp.pb(mp(dec(s.substr(j,3))+151000,0.3));
		if(i==0) tmp.pb(mp(172000,1));
		else if(word[i][0]>='A' && word[i][0]<='Z') tmp.pb(mp(172001,1));
		v[it][it2].pb(tmp);
	}
	return;
}
void cal(int it,int it2){
	int n=v[it][it2].size();
	beam[0][0]=mp(0.0,mp(-1,45));
	rep(i,n){
		//sort(All(beam[i]));reverse(All(beam[i]));
		int wsize=1;if(i>0) wsize=W;
		rep(j,M){
			double t=0.0;
			rep(k,v[it][it2][i].size()) t+=wtag[j][v[it][it2][i][k].fi]*v[it][it2][i][k].se;
			rep(k,wsize){
				int pre=beam[i][k].se.fi;
				int tag1=beam[i][k].se.se,tag2=45;
				if(i>0) tag2=beam[i-1][pre].se.se;
				double t2=t+beam[i][k].fi+wtag[j][173000+tag1]*B+wtag[j][174000+tag1*46+tag2]*T;
				beam[i+1][k*M+j]=mp(t2,mp(k,j));
			}
		}
		sort(beam[i+1],beam[i+1]+M*wsize);reverse(beam[i+1],beam[i+1]+M*wsize);
	}
	rep(j,W){
		int ma=j;pos[j].clear();tagscore[j]=beam[n][j].fi;
		for(int i=n;i>0;i--){
			//pos[j][i-1]=beam[i][ma].se.se;
			pos[j].pb(beam[i][ma].se.se);
			ma=beam[i][ma].se.fi;
		}
		reverse(All(pos[j]));
	}
	return;
}
//ここまで

double comp(vector<int> a,vector<int> b){
	int ok=0,n=a.size();
	rep(i,n){
		if(a[i]==b[i]) ok++;
		else{
			string tag1=en2[a[i]],tag2=en2[b[i]];
			if(tag1.size()<2 || tag2.size()<2) continue;
			if(tag1.substr(0,2)=="NN" && tag2.substr(0,2)=="NN") ok++;
			if(tag1=="NN" && tag2=="JJ") ok++;
			if(tag2=="NN" && tag1=="JJ") ok++;
		}
	}
	return 1.0*ok/n;
}

int main(int argc,char ** argv)
{
	srand(765);
	string s,s0,s1,s2;int a;
	ifstream ifs("wsj00-18.pos");
	ifstream ifs2("wsj19-21.pos");
	ifstream ifs3("train.conll");
	ifstream ifs4("pos.txt");
	rep(i,46){ifs4>>s;en2.pb(s);de2[s]=i;}
	
	//構文解析の部分の学習のみを行う。データから引っ張ってきて学習するだけ
	int t=0;//文の数
	int lin=0;//何列目
	int numbi=0;//biwordの数
	while(1){
		lin++;
		if(!getline(ifs3,s)) break;
		if(s==""){t++;continue;}
		istringstream sin(s);
		rep(i,10){
			if(i==0) sin>>a;
			else if(i==8){sin>>a;ro[0][t].pb(a);}
			else{
				sin>>s1;
				if(i==5){
					//if(s1=="_") break;
					if(s1=="(") s1=="-LCB-";
					if(s1==")") s1=="-RCB-";
					if(de.find(s1)==de.end()){
						de[s1]=en.size()+1;en.pb(s1);
					}
					wo[0][t].pb(de[s1]); 
				}
				if(i==7){
					if(s1=="(") s1="-LRB-";
					if(s1==")") s1="-RRB-";
					/*if(de2.find(s1)==de2.end()){
						de2[s1]=en2.size();en2.pb(s1);
					}*/
					po[0][t].pb(de2[s1]);
				}
			}
		}
	}
	rep(i,t){
		int n=wo[0][i].size();
		rep(j,n) REP(k,j+1,n){
			if(!biword[mp(wo[0][i][j],wo[0][i][k])]){
				numbi++;biword[mp(wo[0][i][j],wo[0][i][k])]=numbi;
			}
			if(!biword[mp(wo[0][i][k],wo[0][i][j])]){
				numbi++;biword[mp(wo[0][i][k],wo[0][i][j])]=numbi;
			}
		}
	}
	rep(l,O){
		rep(i,t){
			parse(wo[0][i],po[0][i]);
			REP(j,1,ro[0][i].size()+1){
				int ok=ro[0][i][j-1],ng=tree[j];
				if(ok==ng) continue;
				rep(k,fea[ok][j].size()){
					wpar[fea[ok][j][k].fi]+=fea[ok][j][k].se;
					w2par[fea[ok][j][k].fi]+=fea[ok][j][k].se*(O*t-(l*t+i));
				}
				rep(k,fea[ng][j].size()){
					wpar[fea[ng][j][k].fi]-=fea[ng][j][k].se;
					w2par[fea[ng][j][k].fi]-=fea[ng][j][k].se*(O*t-(l*t+i));
				}
			}
		}
	}
	rep(i,L){wpar[i]=w2par[i]/(O*t);w2par[i]=wpar[i];}
	rep(i,t){go[0][i].clear();wo[0][i].clear();ro[0][i].clear();po[0][i].clear();}
	//構文解析ここまで
	
	//タグ付けここから
	int n=0;//文の数
	while(getline(ifs,s0)){
		if(go[0][n].size()>0 || wo[0][n].size()>0 || po[0][n].size()>0) cout<<n<<endl;
		istringstream sin(s0);
		while(sin>>s){
			int sh=0;
			rep(i,s.size()){
				if(s[i]=='/'){s[i]=' ';sh++;}
			}
			if(sh>1) continue;
			istringstream sin2(s);
			sin2>>s1>>s2;
			go[0][n].pb(s1);
			if(de2.find(s2)==de2.end()){
				de2[s2]=en2.size();en2.pb(s2);
			}
			po[0][n].pb(de2[s2]);
			if(de.find(s1)==de.end()){
				de[s1]=en.size()+1;en.pb(s1);
			}
			wo[0][n].pb(de[s1]);
		}
		n++;
	}
	rep(i,n) henkan(go[0][i],0,i);
	
	rep(l,K){
		rep(i,n){
			cal(0,i);
			int vs=v[0][i].size();
			rep(j,vs){
				rep(k,v[0][i][j].size()){
					wtag[po[0][i][j]][v[0][i][j][k].fi]+=v[0][i][j][k].se;
					wtag[pos[0][j]][v[0][i][j][k].fi]-=v[0][i][j][k].se;
					w2tag[po[0][i][j]][v[0][i][j][k].fi]+=(K*n-(l*n+i))*v[0][i][j][k].se;
					w2tag[pos[0][j]][v[0][i][j][k].fi]-=(K*n-(l*n+i))*v[0][i][j][k].se;
				}
				if(j>0){
					wtag[po[0][i][j]][173000+po[0][i][j-1]]+=B;
					wtag[pos[0][j]][173000+pos[0][j-1]]-=B;
					w2tag[po[0][i][j]][173000+po[0][i][j-1]]+=(K*n-(l*n+i))*B;
					w2tag[pos[0][j]][173000+pos[0][j-1]]-=(K*n-(l*n+i))*B;
				}
				if(j>1){
					wtag[po[0][i][j]][174000+po[0][i][j-1]*46+po[0][i][j-2]]+=T;
					wtag[pos[0][j]][174000+pos[0][j-1]*46+pos[0][j-2]]-=T;
					w2tag[po[0][i][j]][174000+po[0][i][j-1]*46+po[0][i][j-2]]+=(K*n-(l*n+i))*T;
					w2tag[pos[0][j]][174000+pos[0][j-1]*46+pos[0][j-2]]-=(K*n-(l*n+i))*T;
				}
			}
		}
	}
	rep(j,M) rep(k,N) wtag[j][k]=w2tag[j][k]/K*n;
	//構文解析ここまで
	
	//Rerankerの学習
	rep(l,P){
		rep(i,n){
			cal(0,i);
			int vs=v[0][i].size();
			int mai=0,mai2=0,it=0;double ma=-1e9,ma2=ma,s1=0.0,s2=0.0,s3=0.0;
			rep(j,W){
				double s2=comp(pos[j],po[0][i]);
				if(ma2<s2){ma2=s2;mai2=j;}
				s1+=tagscore[j];
			}
			rep(j,W){
				parse(wo[0][i],pos[j]);
				if(j==ma2){
					ls[i][0]=tagscore[j]/s1;
					REP(k,1,vs+1) rep(l,fea[tree[k]][k].size()){
						feat[i][0].pb(fea[tree[k]][k][l].fi);
					}
				}
				else{
					it++;
					ls[i][it]=tagscore[j]/s1;
					REP(k,1,vs+1) rep(l,fea[tree[k]][k].size()){
						feat[i][it].pb(fea[tree[k]][k][l].fi);
					}
				}
			}
		}
		double lo=-10,hi=10;
		rep(i,100){
			double le=(lo*101+hi*100)/201,ri=(lo*100+hi*101)/201,suml=0,sumr=0;
			rep(j,n) REP(k,1,W){
				suml+=(score[j][0]-score[j][k])*pow(e,)
	}
	rep(i,L) wre[i]=wre[i]/(P*n);
	//cout<<wre[0]<<' '<<wre[1]<<' '<<wre[2]<<endl;
	
	int m=0;//文の数
	while(getline(ifs2,s0)){
		istringstream sin(s0);
		while(sin>>s){
			int sh=0;
			rep(i,s.size()){
				if(s[i]=='/'){s[i]=' ';sh++;}
			}
			if(sh>1) continue;
			istringstream sin2(s);
			sin2>>s1>>s2;
			go[1][m].pb(s1);
			po[1][m].pb(de2[s2]);
			wo[1][m].pb(de[s1]);
		}
		m++;
	}
	rep(i,m) henkan(go[1][i],1,i);
	int ac=0,al=0,upsent=0,downsent=0,oksent=0;
	int wrong[50][50];memset(wrong,0,sizeof(wrong));
	rep(i,m){
		cerr<<i<<endl;
		cal(1,i);int vs=v[1][i].size();
		double ma=-1e9,s1=0.0,s2=0.0;int mai=0;
		vector<pdou> rank;
		rep(j,W){
			cerr<<j<<endl;
			parse(wo[1][i],pos[j]);
			parscore[j]=0.0;
			REP(k,1,vs+1) rep(l,fea[tree[k]][k].size()){
				parscore[j]+=fea[tree[k]][k][l].se*wre[fea[tree[k]][k][l].fi];
			}
			//if(ma<tagscore[j]+parscore[j]){mai=j;ma=tagscore[j]+parscore[j];}
			rank.pb(mp(comp(po[1][i],pos[j]),j));
			s1+=tagscore[j];s2+=parscore[j];
		}
		rep(j,W){
			tagscore[j]/=s1;tagscore[j]/=s2;
			if(ma<tagscore[j]+parscore[j]){mai=j;ma=tagscore[j]+parscore[j];}
		}
		cerr<<i<<endl;
		double smai=comp(po[1][i],pos[mai]),s0=comp(po[1][i],pos[0]);
		if(smai>s0+1e-9) upsent++;
		if(smai<s0-1e-9) downsent++;
		sort(All(rank));reverse(All(rank));if(rank[0].fi-1e-9<smai) oksent++;
		cerr<<i<<endl;
		rep(j,vs){
			if(pos[mai][j]==po[1][i][j]) ac++;
			else wrong[po[1][i][j]][pos[mai][j]]++;
			al++;
		}
	}
	cerr<<"end"<<endl;
	vector<pair<int,string> > wr;
	rep(i,M) rep(j,M) wr.pb(mp(wrong[i][j],en2[i]+" "+en2[j]));
	sort(All(wr));reverse(All(wr));
	rep(i,M*M) cout<<wr[i].fi<<' '<<wr[i].se<<endl;
	cout<<(double)ac/al<<endl;
	cout<<(double)upsent/m<<endl;
	cout<<(double)downsent/m<<endl;
	cout<<(double)oksent/m<<endl;
	return 0;
}
