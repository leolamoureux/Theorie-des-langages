#include "automate.h"
#include "regexp.h"


int main(int argc, char * argv[]){
	
	//Tests première partie
	AUTOMATE A = automate_une_lettre('a');
	automate_ecrire(A,"test_lecture");
	automate_liberer_memoire(A);
	A = automate_lire("test_lecture");
	automate_ecrire(A,"test_ecriture");
	AUTOMATE B = automate_une_lettre('c');
	AUTOMATE C = automate_concatenation(A,B);
	automate_ecrire(C,"test_concatenation");
	AUTOMATE D = automate_disjonction(A,B);
	automate_ecrire(D,"test_disjonction");
	AUTOMATE E = automate_etoile(D);
	automate_ecrire(E,"test_etoile");
	AUTOMATE F = automate_supprimer_epsilon(E);
	automate_ecrire(F,"test_supprimer_epsilon");
	AUTOMATE G = automate_determiniser(F);
	automate_ecrire(G,"test_determiniser");
	automate_liberer_memoire(A);
	automate_liberer_memoire(B);
	automate_liberer_memoire(C);
	automate_liberer_memoire(D);
	automate_liberer_memoire(E);
	automate_liberer_memoire(F);
	
	//Tests seconde partie
	
	if(argc < 1) printf("Usage du programme: automate \"expression régulière\" \n");
	printf("Expression d'entrée: %s\n",argv[1]);
	
	//on verifie l'expression avant de continuer
	if(verif_expr(argv[1]) != 1){
		return 0;
	}
	ADERIV a = construire_arbre_derivation(argv[1]);
	affiche_aderiv(a,0);
	liberer_arbre(a);
	return 0;
}
