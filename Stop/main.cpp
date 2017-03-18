#include <fstream>
#include "primesieve.h"
#include <algorithm>
#include "primesieve.hpp"

using namespace std;

typedef unsigned long long ull;
enum shablony{s_16=15,s_17,s_18,s_19,s_20,s_21,s_22,s_23,s_24,s_25,s_26,s_27,s_28,s_29,s_30,s_31,s_32,s_33};

const int dl_int = 2000000000;
const int chislo_shablonov = 18;
const int max_smew = ((s_33 + 1) >> 1);
const int centr = (s_33 >> 1) - 1;
//const ull max_granica = 18446744030759877397;


//int najdeno[chislo_shablonov];
ull start, end_int, max_stop  ;
unsigned dlina_intervala, factor ;

vector<ull> primes;
bool vypolnitq();
bool init(int nabor[]);
void proverka(int nabor[]);
void vyvod(ull stprime, int nabor[], int st, int shablon);
void prov_ne_poln(int nabor[]);
void prov_styk(int nabor[]);
//void prov_nach_ne_poln(int nabor[]);

inline void proverka_ch(int nabor[], int st, int i){
	for(int j = 1, t = centr + st; j <= 7; j++){
		if(nabor[(t - j) & s_32] != nabor[(t + j) & s_32]) return;
	}
	vyvod(primes[i - s_25], nabor, st + 8, s_16);
	for(int j = 8, t = centr + st; j <= centr; j++){
		if(nabor[(t - j) & s_32] != nabor[(t + j) & s_32]) return;
		vyvod(primes[i - s_18 - j], nabor, st + s_16 - j, s_16 + ((j - 7) << 1));
	}
}

inline void proverka_nch(int nabor[], int st, int i){
	for(int j = 0, t = centr + st; j <= 7; j++){
		if(nabor[(t - j) & s_32] != nabor[(t + j + 1) & s_32]) return;
	}
	vyvod(primes[i - s_25], nabor, st + 8, s_17);
	for(int j = 8, t = centr + st; j <= centr; j++){
		if(nabor[(t - j) & s_32] != nabor[(t + j + 1) & s_32]) return;
		vyvod(primes[i - s_18 - j], nabor, st + s_16 - j, s_17 + ((j - 7) << 1));
	}
}

inline void prov_nach(int nabor[], int i, int k){
	for(int j = 0; j < (i >> 1); j++) if(nabor[k + j] != nabor[i - 1 + k - j]) return;
	vyvod(primes[k], nabor, k, i);
}

int main() {
	ifstream fin("in");
	if (!fin) return 1;
	fin >> start >> max_stop >> factor;
	fin.close();
	fstream fout("out", ios::out | ios::app);
	fout.close();
	dlina_intervala = dl_int / factor & 0xfffffffe;
	while (vypolnitq());
	return 0;
}


bool vypolnitq(){
	end_int = min(start + dlina_intervala, max_stop);
	primes.clear();
	primesieve::generate_primes(start, end_int, &primes);
	if(primes.size() <= s_16) return false;
	int nabor[s_33];
	if(!init(nabor)) return false;
	proverka(nabor);
	return true;
}

bool init(int nabor[]){
	static bool inicial;
	if(inicial){
		if(primes.size() <= s_33){
			if(primes.size() == s_33){
//				if(max_stop > max_granica) prov_ne_poln(nabor);
//				else prov_styk(nabor);
				prov_styk(nabor);
			}
			return false;
		}
		for(int i = 0; i < s_33; i++) nabor[i] = int(primes[i + 1] - primes[i]);
	}else{
//		if(primes.size() <= s_33){
//			prov_nach_ne_poln(nabor);
//			return false;
//		}
		for(int i = 0; i < s_33; i++) nabor[i] = int(primes[i + 1] - primes[i]);
		for(int i = s_16; i <= s_30; i++)
			for(int k = 0; k < max_smew - ((i + 1) >> 1); k++) prov_nach(nabor, i, k);
		inicial = true;
	}
	return true;
}

void proverka(int nabor[]){
	int st = 0;
	for(unsigned i = s_33;; i++){
		proverka_ch(nabor, st, i);
		proverka_nch(nabor, st, i);
		if(i >= primes.size() - 1) break;
		nabor[st] = int(primes[i + 1] - primes[i]);	
		st = (st + 1) & s_32;
	}
	start = primes[primes.size() - s_33] - 1;
}

void vyvod(ull stprime, int nabor[], int st, int shablon){
	ofstream fout("out", ios::out | ios::app);
//	fout << stprime << " 0";
	fout << stprime << ' ' << (shablon + 1);
	for(int i = 0, sum = 0; i < shablon; i++) fout << ' ' << (sum += nabor[(st + i) & s_32]);
	fout <<"\r\n";
	fout.close();
//	najdeno[shablon - s_16]++;
}

void prov_ne_poln(int nabor[]){
	for(int i = 0; i < s_32; i++) nabor[i] = int(primes[i + 1] - primes[i]);
	for(int i = s_16; i <= s_31; i++){
		for(int j = s_16 - ((i + 1) >> 1); j <= s_20 - ((i + 2) >> 1); j++){
			for(int k = 0; k < (i >> 1); k++){if(nabor[k + j] != nabor[i - 1 - k + j]) goto next;}
			vyvod(primes[j], nabor, j, i);
next:		;
		}
	}
}

void prov_styk(int nabor[]){
	vector<ull> temp_primes;
	primesieve::generate_n_primes(s_33, max_stop, &temp_primes);
	for(int i = 0; i < s_33; i++) primes.push_back(temp_primes[i]);
	int st = 0;
	for(unsigned i = s_33;; i++){
		proverka_ch(nabor, st, i);
		proverka_nch(nabor, st, i);
		if(i >= primes.size() - 1) break;
		nabor[st] = int(primes[i + 1] - primes[i]);	
		st = (st + 1) & s_32;
	}
	start = max_stop;
}

/*
void prov_nach_ne_poln(int nabor[]){
	int raz = primes.size() - 1;
	for(int i = 0; i < raz; i++) nabor[i] = int(primes[i + 1] - primes[i]);
	for(int i = s_16; i <= raz; i++){
		for(int j = 0; j <= raz - i; j++){
			for(int k = 0; k < (i >> 1); k++){if(nabor[k + j] != nabor[i - 1 - k + j]) goto next;}
			vyvod(primes[j], nabor, j, i);
next:		;
		}
	}
}
*/