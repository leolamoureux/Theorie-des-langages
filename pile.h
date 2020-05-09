#include <stdio.h>
#include <stdlib.h>

typedef enum{ //les différents type de symboles dans la grammaire
	S,A,B,C,D,E,F,CAR,PARO,PARF,PLUS,POINT,ETOILE
}STATE;

void affiche_state(STATE s);//affiche le nom d'un état

typedef struct{
	STATE *contenu;//contenu de la pile
	int sommet;//position du sommet de la pile
	int taille_max;//taille maximum de la pile
}PILE;


int est_vide(PILE p);
PILE nouvelle_pile(int taille_max);//renvoie une nouvelle pile de taille au plus taille_max
PILE empiler(PILE p, STATE s);
STATE depiler(PILE *p);
void affiche_pile(PILE p);//affiche le contenu de la pile
void liberer_pile(PILE p);//libère la mémoire utilisée par la pile

