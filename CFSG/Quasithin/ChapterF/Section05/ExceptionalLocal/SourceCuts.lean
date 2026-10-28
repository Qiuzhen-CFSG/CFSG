module

public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.Data
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Theory.ElementaryAbelian.Basic

/-!
# Explicit proof cuts for the exceptional local analysis

These predicates state intermediate conclusions, not additional hypotheses of
F.4.31 and not proved book theorems. The fusion producer must construct
`FusionFacts` from `Source.Hypotheses` and `Source.Exceptional`; the normalizer
producer then proves `NormalizerFacts`. They allow the subsequent transfer
argument to be developed without replacing the source theorem by an assumed
recognition statement. The assembly owner must discharge both predicates.

The involution `t` is characterized by the literal subgroup [Q₂,f]; this keeps
its marking independent of any later orthogonal model equivalence. All cores,
normalizers, centralizers and quotients use the original ambient inclusions.

Source: Aschbacher--Smith F.4.33--37, F.5.3--4, printed pp.291--294, 300--301.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal

open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
local notation "C2" => Multiplicative (ZMod 2)
local notation "S4" => Equiv.Perm (Fin 4)
local notation "S5" => Equiv.Perm (Fin 5)
local notation "S3" => Equiv.Perm (Fin 3)
local notation "D8" => DihedralGroup 4

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

def rootElement (z : pointParabolic 1 hn) : G := i (c.left (Source.pointInclusion z))

def Tcentralizer (t : G) : Subgroup G :=
  Source.sylowImage c i ⊓ centralizer ({t} : Set G)

/-- The intersection of a class with a specified literal subgroup. -/
def classIntersection (x : G) (K : Subgroup G) := {y : K // IsConj x y.val}

/-- F.4.33--37 and the source fusion information of F.5.3.
Every field is an obligation of the source fusion producer. -/
structure FusionFacts (z : pointParabolic 1 hn) (t : G) : Prop where
  sylow : ∃ S : Sylow 2 G, (S : Subgroup G) = Source.sylowImage c i
  sylow_card : Nat.card (Source.sylowImage c i) = 128
  tf_card : Nat.card (Tf c i) = 32
  tf_sylow : ∀ b, ∃ S : Sylow 2 (E c i b),
    (S : Subgroup (E c i b)).map (E c i b).subtype = TfImage c i
  root_centralizer : centralizer ({rootElement c i z} : Set G) = M c i false
  t_mem : t ∈ Source.sylowImage c i
  t_order : orderOf t = 2
  t_commutator : ⁅Q c i true, zpowers (Source.graphElement c i)⁆ = zpowers t
  t_commutes_graph : Commute t (Source.graphElement c i)
  t_commutes_root : Commute t (rootElement c i z)
  t_sylow : ∃ S : Sylow 2 (centralizer ({t} : Set G)),
    (S : Subgroup (centralizer ({t} : Set G))) =
      (Source.sylowImage c i).subgroupOf (centralizer ({t} : Set G))
  t_centralizer_iso : Nonempty (Tcentralizer c i t ≃* D8 × D8)
  two_classes : ∀ x : G, orderOf x = 2 →
    IsConj (rootElement c i z) x ∨ IsConj (Source.graphElement c i) x
  graph_fuses_t : IsConj (Source.graphElement c i) t
  root_fuses_graph_root : IsConj (rootElement c i z)
    (Source.graphElement c i * rootElement c i z)
  root_fuses_graph_t_root : IsConj (rootElement c i z)
    (Source.graphElement c i * t * rootElement c i z)
  t_fuses_t_root : ∃ y ∈ Source.sylowImage c i,
    y * t * y⁻¹ = t * rootElement c i z
  E_iso : ∀ b, Nonempty (E c i b ≃* (C2 × C2) × S4)
  Dendpoint_iso : ∀ b, Nonempty (Dendpoint c i b ≃* C2 × S4)
  A_elementary : ∀ b, IsElementaryAbelian 2 (A c i b)
  A_card : ∀ b, Nat.card (A c i b) = 16
  root_mem_A : ∀ b, rootElement c i z ∈ A c i b
  root_class_A_point : Nat.card (classIntersection (rootElement c i z) (A c i false)) = 5
  root_class_A_plane : Nat.card (classIntersection (rootElement c i z) (A c i true)) = 9
  root_class_Q_plane : Nat.card (classIntersection (rootElement c i z) (Q c i true)) = 5

/-- The literal quotient N_G(Q₂)/Q₂. -/
abbrev planeCoreNormalizerQuotient :=
  normalizer (Q c i true : Set G) ⧸
    (Q c i true).subgroupOf (normalizer (Q c i true : Set G))

/-- F.5.4 with the additional local intersections used in F.5.5.
The Sylow argument uses a supplied `R` containing the literal `Tf`. -/
structure NormalizerFacts (z : pointParabolic 1 hn) (t : G)
    (R : Sylow 2 (C c i)) : Prop where
  self_centralizer : ∀ b, centralizer (A c i b : Set G) = A c i b
  R_iso : Nonempty (Rimage c i R ≃* D8 × D8)
  R_normalizes_E : ∀ b, Rimage c i R ≤ normalizer (E c i b : Set G)
  ER_iso : ∀ b, Nonempty ((E c i b ⊔ Rimage c i R : Subgroup G) ≃* D8 × S4)
  point_quotient : Nonempty (normalizerQuotient c i false ≃* S5)
  plane_quotient : Nonempty (normalizerQuotient c i true ≃* S3 × S3)
  Q_quotient : Nonempty (planeCoreNormalizerQuotient c i ≃* S5)
  elementary_bound : ∀ B : Subgroup G, B ≤ Source.sylowImage c i →
    IsElementaryAbelian 2 B → Nat.card B ≤ 16
  elementary_list : ∀ y ∈ Source.sylowImage c i, y ∉ Tcentralizer c i t →
    ∀ B : Subgroup G, (B ≤ Source.sylowImage c i ∧ IsElementaryAbelian 2 B ∧
      Nat.card B = 16) ↔
      B = A c i false ∨ B = A c i true ∨
        B = (A c i true).map (MulAut.conj y).toMonoidHom ∨ B = Q c i true
  plane_intersection : ∀ y ∈ Source.sylowImage c i, y ∉ Tcentralizer c i t →
    A c i true ⊓ (A c i true).map (MulAut.conj y).toMonoidHom =
      zpowers (rootElement c i z) ⊔ zpowers t
  joint_centralizer : centralizer ({rootElement c i z, t} : Set G) = Tcentralizer c i t
  local_plane_normalizer : M c i false ⊓ normalizer (A c i true : Set G) = Tcentralizer c i t
  transvection : ∀ b, ∃ g ∈ normalizer (A c i b : Set G),
    ((centralizer ({g} : Set G)).subgroupOf (A c i b)).index = 2

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
