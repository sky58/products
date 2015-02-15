//オセロプログラム
//同枠のparameter.txtから評価用パラメータを読み込んで使用している
//石を置きたい場所をタイプする
#include<vector>
#include<cmath>
#include<map>
#include<cstdlib>
#include<iostream>
#include<sstream>
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
typedef pair<int,int> pint;
#define All(s) s.begin(),s.end()
#define rAll(s) s.rbegin(),s.rend()
#define REP(i,a,b) for(int i=a;i<b;i++)
#define rep(i,n) REP(i,0,n)
int dx[8]={-1,-1,-1,0,0,1,1,1},dy[8]={-1,0,1,-1,1,-1,0,1};
int edx[4]={0,7,7,0},edy[4]={0,0,7,7},eddx[4]={1,0,-1,0},eddy[4]={0,1,0,-1};
int xx[4]={1,6,6,1},xy[4]={1,1,6,6};
int ban[100][8][8];//現在・過去・未来の盤面を保存
int w[8][8];
int INF=1000000000;
int a,b;
clock_t start,end;
double kaweight[2]={4000,4000};
double weight[2]={10000,10000};

//考慮時間の制限
bool timelimit(void){
	end=clock();
	if((double)(end-start)/CLOCKS_PER_SEC>2.9) return true;
	else return false;
}

//添字を棋譜に直す
string dec(void){
	if(a>7) return "PA";
	string s="  ";
	s[0]=(a+'a');s[1]=(b+'1');return s;
}

//棋譜を添字に直す
void enc(string s){
	if(s=="matta"){a=9;b=9;return;}
	if(s=="PA" || s=="pa"){a=8;b=8;return;}
	if(s[0]>='A' && s[0]<='Z') a=s[0]-'A';else a=s[0]-'a';
	b=s[1]-'1';return;
}

//盤面内に収まるかの判定
bool in(int x,int y){
	if(x<0 || y<0 || x>7 || y>7) return false;return true;
}

//盤面の表示
void printban(int turn){
	cout<<' ';
	rep(i,8){
		char c=('1'+i);
		cout<<c;
	}
	cout<<endl;
	rep(i,8){
		char c=('a'+i);
		cout<<c;
		rep(j,8){
			if(ban[turn][i][j]==0) cout<<".";
			if(ban[turn][i][j]==1) cout<<"x";
			if(ban[turn][i][j]==2) cout<<"o";
		}
		cout<<endl;
	}
	return;
}

//置けるかどうかの判定（ついでに置いた後のシュミレート）
bool can(int x,int y,int turn,int whoturn){
	if(x==8 && y==8){
		memcpy(ban[turn+1],ban[turn],sizeof(ban[turn]));return true;
	}
	if(!in(x,y)) return false;
	if(ban[turn][x][y]>0) return false;
	int f=1;
	rep(i,8){
		int nx=x+dx[i],ny=y+dy[i];
		if(!in(nx,ny)) continue;
		if(ban[turn][nx][ny]==3-whoturn) f=0;
	}
	if(f>0) return false;
	memcpy(ban[turn+1],ban[turn],sizeof(ban[turn]));
	ban[turn+1][x][y]=whoturn;
	rep(i,8){
		REP(j,1,8){
			int nx=x+dx[i]*j,ny=y+dy[i]*j;
			if(!in(nx,ny)) break;
			if(ban[turn+1][nx][ny]==whoturn){
				if(j>1) f=1;
				REP(k,1,j) ban[turn+1][x+dx[i]*k][y+dy[i]*k]=whoturn;
				break;
			}
			if(ban[turn+1][nx][ny]==0) break;
		}
	}
	if(f>0) return true;return false;
}

//ゲームの終了の判定
bool gameEnd(int turn){
	rep(i,8) rep(j,8){
		if(can(i,j,turn,1) || can(i,j,turn,2)) return false;
	}
	return true;
}

//評価関数
double func(int turn,int whoturn,int key){
	double ret=0;
	rep(i,8) rep(j,8){
		if(ban[turn][i][j]==whoturn) ret+=w[i][j]+weight[key];
		if(ban[turn][i][j]==3-whoturn) ret-=w[i][j]+weight[key];
	}
	rep(i,4){
		int ma=8,k;
		rep(j,8){
			for(k=0;k<ma;k++){
				if(ban[turn][edx[i]+eddx[i]*j][edy[i]+eddy[i]*k]!=ban[turn][edx[i]][edy[i]]) break;
			}
			ma=min(ma,k);
			if(ban[turn][edx[i]][edy[i]]==whoturn) ret+=ma*kaweight[key];
			else if(ban[turn][edx[i]][edy[i]]==3-whoturn) ret-=ma*kaweight[key];
		}
	}
	if(turn%2+1!=whoturn) ret*=-1;
	return ret;
}

//評価関数その2（単にゲームが終わってる時に石を数えるだけ）
double func2(int turn,int whoturn){
	double ret=0;
	rep(i,8) rep(j,8){
		if(ban[turn][i][j]==whoturn) ret++;
		if(ban[turn][i][j]==3-whoturn) ret--;
	}
	if(turn%2+1!=whoturn) ret*=-1;
	//cout<<ret<<endl;
	return ret;
}

//alpha-beta法
double alphabeta(int turn,int whoturn,int depth,int key,double alpha,double beta){
	if(gameEnd(turn)) return func2(turn,whoturn);
	if(depth==0) return func(turn,whoturn,key);
	int f=0;
	rep(i,8) rep(j,8){
		if(timelimit()) return alpha;
		if(can(i,j,turn,turn%2+1)){
			f=1;
			alpha=max(alpha,-alphabeta(turn+1,whoturn,depth-1,key,-beta,-alpha));
			if(beta<=alpha) return beta;
		}
	}
	if(f<1){
		can(8,8,turn,turn%2+1);
		alpha=max(alpha,-alphabeta(turn+1,whoturn,depth-1,key,-beta,-alpha));
		if(beta<=alpha) return beta;
	}
	return alpha;
}

//コンピュータ側の指し手を調べる
void ai(int turn,int key){
	a=8;b=8;
	rep(depth,20){
		double ma=-INF;int whoturn=turn%2+1,nowa=8,nowb=8;
		rep(i,8) rep(j,8){
			if(timelimit()) return;
			if(can(i,j,turn,whoturn)){
				int funcret=-alphabeta(turn+1,whoturn,depth,key,-INF,-ma);
				if(funcret>ma){nowa=i;nowb=j;ma=funcret;}
				//cout<<i<<' '<<j<<' '<<depth<<' '<<funcret<<endl;
			}
		}
		a=nowa;b=nowb;
	}
	return;
}

//ゲームをシュミレーション
pint game(void)
{
	int turn=0,user=2,kuro=0,siro=0;string s;
	memset(ban,0,sizeof(ban));ban[0][3][3]=ban[0][4][4]=2;ban[0][3][4]=ban[0][4][3]=1;
	cout<<"Which play(Black(x):0 White(o):1 Auto:2)?"<<endl;cin>>user;
	for(;;turn++){
		if(gameEnd(turn)) break;
		printban(turn);
		if(turn%2==user){
			while(1){
				cin>>s;enc(s);
				if(a==9 && b==9){turn-=3;break;}
				if(!can(a,b,turn,turn%2+1)) cout<<"Cannot"<<endl;
 				else break;
			}
		}
		else{
			start=clock();
			ai(turn,turn%2);
			can(a,b,turn,turn%2+1);
			cout<<dec()<<endl;
		}
	}
	printban(turn);
	rep(i,8) rep(j,8){
		if(ban[turn][i][j]==1) kuro++;if(ban[turn][i][j]==2) siro++;
	}
	printf("Brack:%d White:%d\n",kuro,siro);
	return mp(kuro,siro);
}

int main()
{
	FILE *fp=fopen("parameter.txt","r");
	rep(i,8) rep(j,8) fscanf(fp,"%d",&w[i][j]);
	game();
	return 0;
}
