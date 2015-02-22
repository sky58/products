//WSJコーパスを学習・評価に用いた品詞タグ(POSタグ)付け
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
#define All(s) s.begin(),s.end()
#define rAll(s) s.rbegin(),s.rend()
#define REP(i,a,b) for(int i=a;i<b;i++)
#define rep(i,n) REP(i,0,n)
#define N 180000//特徴ベクトルの次元数
#define M 45//品詞の種類
#define K 5//学習を繰り返す回数
int n;//学習した単語の数
int m;//テストした単語の数
int o=0;//学習した単語の種類
double B=1.0;//タグのbi-gramの重み
double T=1.0;//タグのtri-gramの重み
int W=10;//ビーム幅
double INF=1e10;

map<string,int> de,de2;
vector <string> en,en2;
vector <string> go[2],hin[2];
vector <int> hinint[2],goint[2],sen[2];
vector <vector <pint> > v[2][40000];//各文ごとのフィーチャー
double w[M+2][N+2],w2[M+2][N+2];
int pos[300];//タグ付けの結果
vector<tint> beam[300];
map<pint,int> biword;

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
		//if(i>1) tmp.pb(mp(de[word[i-2]]+180000,0.8));
		v[it][it2].pb(tmp);
	}
	return;
}

void cal(int it,int it2){
	int n=v[it][it2].size();
	rep(i,n+10) beam[i].clear();beam[0].pb(mp(0.0,mp(-1,45)));
	beam[0].pb(mp(0.0,mp(-1,45)));
	rep(i,n){
		sort(All(beam[i]));reverse(All(beam[i]));
		rep(j,M){
			double t=0.0;
			rep(k,v[it][it2][i].size()) t+=w[j][v[it][it2][i][k].fi]*v[it][it2][i][k].se;
			rep(k,min(W,(int)beam[i].size())){
				int pre=beam[i][k].se.fi;
				int tag1=beam[i][k].se.se,tag2=45;
				if(i>0) tag2=beam[i-1][pre].se.se;
				double t2=t+beam[i][k].fi+w[j][173000+tag1]*B+w[j][174000+tag1*46+tag2]*T;
				beam[i+1].pb(mp(t2,mp(k,j)));
			}
		}
	}
	sort(All(beam[n]));reverse(All(beam[n]));
	int ma=0;
	for(int i=n;i>0;i--){
		pos[i-1]=beam[i][ma].se.se;ma=beam[i][ma].se.fi;
	}
	return;
}

int main(int argc,char ** argv)
{
	srand(765);
	string s,s0,s1,s2;
	memset(w,0,sizeof(w));
	memset(w2,0,sizeof(w2));
	ifstream ifs("wsj00-18.pos");
	ifstream ifs2("wsj19-21.pos");
	sen[0].pb(0);
	while(getline(ifs,s0)){
		istringstream sin(s0);
		while(sin>>s){
			int sh=0;
			rep(i,s.size()){
				if(s[i]=='/'){s[i]=' ';sh++;}
			}
			if(sh>1) continue;
			istringstream sin2(s);
			sin2>>s1>>s2;
			go[0].pb(s1);hin[0].pb(s2);
			if(de2.find(s2)==de2.end()){
				de2[s2]=en2.size();en2.pb(s2);
			}
			hinint[0].pb(de2[s2]);
			if(de.find(s1)==de.end()){
				o++;de[s1]=o;en.pb(s1);
			}
			goint[0].pb(de[s1]);
		}
		sen[0].pb(go[0].size());
	}
	int n=sen[0].size()-1;
	rep(i,n){
		int t=sen[0][i+1]-sen[0][i],st=sen[0][i];
		rep(j,t-1) biword[mp(goint[0][st+j],goint[0][st+j+1])]++;
	}
	//rep(i,sen[0][n]-1) biword[mp(goint[0][i],goint[0][i+1])]=1;
	cout<<biword.size()<<endl;return 0;
	rep(i,n){
		vector <string> word;REP(j,sen[0][i],sen[0][i+1]) word.pb(go[0][j]);
		henkan(word,0,i);
	}
	rep(l,K){
		rep(i,n){
			cal(0,i);int vs=v[0][i].size();
			rep(j,vs){
				int nowp=j+sen[0][i];
				rep(k,v[0][i][j].size()){
					w[hinint[0][nowp]][v[0][i][j][k].fi]+=v[0][i][j][k].se;
					w[pos[j]][v[0][i][j][k].fi]-=v[0][i][j][k].se;
					w2[hinint[0][nowp]][v[0][i][j][k].fi]+=(K*n-(l*n+i))*v[0][i][j][k].se;
					w2[pos[j]][v[0][i][j][k].fi]-=(K*n-(l*n+i))*v[0][i][j][k].se;
				}
				if(j>0){
					w[hinint[0][nowp]][173000+hinint[0][nowp-1]]+=B;
					w[pos[j]][173000+pos[j-1]]-=B;
					w2[hinint[0][nowp]][173000+hinint[0][nowp-1]]+=(K*n-(l*n+i))*B;
					w2[pos[j]][173000+pos[j-1]]-=(K*n-(l*n+i))*B;
				}
				if(j>1){
					w[hinint[0][nowp]][174000+hinint[0][nowp-1]*46+hinint[0][nowp-2]]+=T;
					w[pos[j]][174000+pos[j-1]*46+pos[j-2]]-=T;
					w2[hinint[0][nowp]][174000+hinint[0][nowp-1]*46+hinint[0][nowp-2]]+=(K*n-(l*n+i))*T;
					w2[pos[j]][174000+pos[j-1]*46+pos[j-2]]-=(K*n-(l*n+i))*T;
				}
			}
		}
	}
	rep(j,M) rep(k,N) w[j][k]=w2[j][k]/K*n;
	
	sen[1].pb(0);
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
			go[1].pb(s1);hin[1].pb(s2);
			hinint[1].pb(de2[s2]);
			goint[1].pb(de[s1]);
		}
		sen[1].pb(go[1].size());
	}
	int m=sen[1].size()-1;
	rep(i,m){
		vector <string> word;REP(j,sen[1][i],sen[1][i+1]) word.pb(go[1][j]);
		henkan(word,1,i);
	}
	int ac=0;int wrong[50][50];memset(wrong,0,sizeof(wrong));
	rep(i,m){
		cal(1,i);int vs=v[1][i].size();
		rep(j,vs){
			//cout<<pos[j]<<' '<<hinint[1][j+sen[1][i]]<<endl;
			if(pos[j]==hinint[1][j+sen[1][i]]) ac++;
			else wrong[hinint[1][j+sen[1][i]]][pos[j]]++;
		}
	}
	//vector<pair<int,string> > wr;
	//rep(i,M) rep(j,M) wr.pb(mp(wrong[i][j],en2[i]+" "+en2[j]));
	//sort(All(wr));reverse(All(wr));
	//rep(i,M*M) cout<<wr[i].fi<<' '<<wr[i].se<<endl;
	cout<<(double)ac/sen[1][m]<<endl;
	return 0;
}
