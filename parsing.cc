//最小有向全域木アルゴリズムを用いた係り受け構文解析器
//CoNLL08SharedTaskのフォーマットを使用
//学習用データ(train.conll)とテスト用データ(devel.conll)を同じフォルダに置いて実行する
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
#include<cstdlib>
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
typedef double typ;
#define All(s) s.begin(),s.end()
#define rAll(s) s.rbegin(),s.rend()
#define REP(i,a,b) for(int i=a;i<b;i++)
#define rep(i,n) REP(i,0,n)
#define N 19100000//フィーチャーの数
#define M 10//学習の回数
#define W 300//一文における最大の単語の数

//単語・タグと数字の変換用
map<string,int> de,de2;
vector <string> en,en2;

//単語やタグの数
int numsum=0,numword=0,numpos=0;

//学習用・開発用データの入れ場所
vector <int> ro[2][40000],wo[2][40000],po[2][40000];

vector<pint> fea[W][W];//フィーチャーベクトル
double w[N];//重みベクトル
double w2[N];//平均化ベクトル
vector<int> tree;//構文木
typ inf=1e9,CONST=1e5;
map<pint,int> biword;

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
		rep(k,fea[i][j].size()) wei+=w[fea[i][j][k].fi]*fea[i][j][k].se;
		gr[i][j]=-wei;if(i<1) gr[i][j]+=CONST;
	}
	tree=dmst(0,n+1,gr);
	double ret=+CONST;
	REP(j,1,n+1) ret-=gr[tree[j]][j];
	return ret;
}

int main(int argc, char ** argv)
{
	string s,s1;int a;
	ifstream ifs3("train.conll");
	ifstream ifs4("pos.txt");
	ifstream ifs5("devel.conll");
	rep(i,46){ifs4>>s;en2.pb(s);de2[s]=i;}
	
	int t=0;//文の数
	int lin=0;//何列目
	int numbi=0;//wordのbigram
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
	//cout<<numbi<<endl;return 0;
	rep(l,M){
		rep(i,t){
			parse(wo[0][i],po[0][i]);
			REP(j,1,ro[0][i].size()+1){
				int ok=ro[0][i][j-1],ng=tree[j];
				if(ok==ng) continue;
				rep(k,fea[ok][j].size()){
					w[fea[ok][j][k].fi]+=fea[ok][j][k].se;
					w2[fea[ok][j][k].fi]+=fea[ok][j][k].se*(M*t-(l*t+i));
				}
				rep(k,fea[ng][j].size()){
					w[fea[ng][j][k].fi]-=fea[ng][j][k].se;
					w2[fea[ng][j][k].fi]-=fea[ng][j][k].se*(M*t-(l*t+i));
				}
			}
		}
	}
	rep(i,N) w[i]=w2[i]/(t*M);
	
	t=0;//文の数
	while(1){
		if(!getline(ifs5,s)) break;
		if(s==""){t++;continue;}
		istringstream sin(s);
		rep(i,10){
			if(i==0) sin>>a;
			else if(i==8){sin>>a;ro[1][t].pb(a);}
			else{
				sin>>s1;
				if(i==5){
					//if(s1=="_") break;
					if(s1=="(") s1=="-LCB-";
					if(s1==")") s1=="-RCB-";
					if(de.find(s1)==de.end()){
						de[s1]=en.size()+1;en.pb(s1);
					}
					wo[1][t].pb(de[s1]); 
				}
				if(i==7){
					if(s1=="(") s1="-LRB-";
					if(s1==")") s1="-RRB-";
					/*if(de2.find(s1)==de2.end()){
						de2[s1]=en2.size();en2.pb(s1);
					}*/
					po[1][t].pb(de2[s1]);
				}
			}
		}
	}
	int ok=0,ng=0;
	rep(i,t){
		parse(wo[1][i],po[1][i]);
		rep(j,ro[1][i].size()){
			if(ro[1][i][j]==tree[j+1]) ok++;else ng++;
		}
	}
	cout<<1.0*ok/(ok+ng)<<endl;
	return 0;
}
