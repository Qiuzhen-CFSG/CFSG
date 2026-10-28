module

public import CFSG.Quasithin.ChapterG.Section02.Setup

/-!
# The three marked conjugates in G.2.5

These constructions are separate from the two-conjugate constructions in
`Setup`. In particular, the middle denominator is the intersection of all
three copies of U. The third term is initially defined by a join; its
identification with the printed product requires the normalization proof.
An expression such as W/S₃ always denotes an image in S/S₃.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma G.2.5, printed pp.335–336, PDF pp.346–347.
-/

@[expose] public section
open Subgroup

namespace CFSG.Quasithin.ChapterG.Section02.LinearThree
open Setup
variable {G : Type*} [Group G]

def I (D : Setup G) (g h : G) : Subgroup G :=
  (D.U ⊔ conjugate D.U g) ⊔ conjugate D.U h

def S (D : Setup G) (g h : G) : Subgroup G := (I D g h).pCoreIn 2

def W (D : Setup G) (g h : G) : Subgroup G := D.U ⊓ S D g h

def S₂ (D : Setup G) (g h : G) : Subgroup G :=
  (D.U ⊓ conjugate D.U g) ⊓ conjugate D.U h

def S₃ (D : Setup G) (g h : G) : Subgroup G :=
  ((W D g h ⊓ conjugate (W D g h) g) ⊔
    (W D g h ⊓ conjugate (W D g h) h)) ⊔
    (conjugate (W D g h) g ⊓ conjugate (W D g h) h)

abbrev LowerQuotient (D : Setup G) (g h : G) :=
  S₃ D g h ⧸ (S₂ D g h).subgroupOf (S₃ D g h)

abbrev UpperQuotient (D : Setup G) (g h : G) :=
  S D g h ⧸ (S₃ D g h).subgroupOf (S D g h)

/-- The image of an ambient subgroup in the actual upper quotient. There
is deliberately no containment of the denominator in that subgroup. -/
def upperImage (D : Setup G) (g h : G)
    [((S₃ D g h).subgroupOf (S D g h)).Normal] (A : Subgroup G) :
    Subgroup (UpperQuotient D g h) :=
  (A.subgroupOf (S D g h)).map
    (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)))

/-- The image of an ambient subgroup in the actual dual layer. -/
def lowerImage (D : Setup G) (g h : G)
    [((S₂ D g h).subgroupOf (S₃ D g h)).Normal] (A : Subgroup G) :
    Subgroup (LowerQuotient D g h) :=
  (A.subgroupOf (S₃ D g h)).map
    (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)))

end CFSG.Quasithin.ChapterG.Section02.LinearThree
