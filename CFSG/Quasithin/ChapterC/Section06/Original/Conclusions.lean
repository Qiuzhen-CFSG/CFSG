module
public import CFSG.Quasithin.ChapterC.Section06.Original.Definitions
public import CFSG.Quasithin.ChapterC.Section06.CubicGlobal
public import CFSG.Quasithin.ChapterC.Section06.AlternatingGlobal
public import CFSG.Quasithin.ChapterC.Section06.CubicPairGlobal
/-!
# The conclusions of original C.6.1 on the literal subgroups

The common conclusion records (1) and (5). The three branch predicates
record the natural, single A₃ and four-family alternatives, including
(3), (4), and all possibilities in (6). The paired A₃ branch retains its
actual two commuting blocks, rather than only an abstract group model.
Source: Aschbacher--Smith C.6.1(1)--(6), printed pp.164--166.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06.Original
variable {G : Type*} [Group G]

def Common (H Λ : Subgroup G) : Prop :=
  let R := Λ ⊓ H
  let L := (pResidual 2 H).map H.subtype
  let Q := H.pCoreIn 2
  let N₀ := Λ ⊓ normalizer (R : Set G)
  R.relIndex N₀ = 2 ∧ ChapterB.baumann R = elementaryAbelianMaxJ R ∧
    Q = L.pCoreIn 2 ⊔ (R ⊓ centralizer (L : Set G)) ∧
    ∀ x ∈ N₀, x ∉ R → elementaryAbelianMaxJ R = Q ⊔ Q.map (MulAut.conj x⁻¹).toMonoidHom

def PairFamily (H Λ : Subgroup G) : Prop :=
  let R := Λ ⊓ H
  let Q := H.pCoreIn 2
  ∀ x ∈ Λ ⊓ normalizer (R : Set G), x ∉ R →
    elementaryAbelianMaxSubgroups R = {Q,Q.map (MulAut.conj x⁻¹).toMonoidHom}

def GlobalIndexTwo (H Λ : Subgroup G) : Prop :=
  (Λ ⊓ H).relIndex Λ = 2 ∧ elementaryAbelianMaxJ (Λ ⊓ H) = elementaryAbelianMaxJ Λ

def FourFamily (H Λ : Subgroup G) : Prop :=
  let R := Λ ⊓ H
  let Q := H.pCoreIn 2
  ∀ x ∈ Λ ⊓ normalizer (R : Set G), x ∉ R →
    ∃ A : Subgroup G, ∃ r ∈ R, r ∉ elementaryAbelianMaxJ R ∧ Q.relIndex A = 2 ∧
      elementaryAbelianMaxSubgroups R =
        {Q,Q.map (MulAut.conj x⁻¹).toMonoidHom,A,A.map (MulAut.conj r⁻¹).toMonoidHom}

def DihedralNormalizer (H Λ : Subgroup G) : Prop :=
  let R := Λ ⊓ H
  let S := elementaryAbelianMaxJ R
  let N₀ := Λ ⊓ normalizer (R : Set G)
  let N₁ := Λ ⊓ normalizer (N₀ : Set G)
  ∃ hn : (S.subgroupOf N₁).Normal, letI := hn
    Nonempty ((N₁ ⧸ S.subgroupOf N₁) ≃* DihedralGroup 4) ∧
    ∃ A ∈ elementaryAbelianMaxSubgroups R, (H.pCoreIn 2).relIndex A = 2 ∧
      Nat.card R ≤ Nat.card (Λ ⊓ normalizer ((H.pCoreIn 2 ⊔ A : Subgroup G) : Set G) : Subgroup G)

def CubicPair (L : Subgroup G) : Prop :=
  ∃ K₁ K₂ : Subgroup G, K₁ ≠ K₂ ∧ IsAlternatingBlock K₁ 3 ∧ IsAlternatingBlock K₂ 3 ∧
    K₂ ≤ centralizer (K₁ : Set G) ∧ K₁ ⊔ K₂ = L

/-- The original theorem, expressed as the three source geometries. -/
def Conclusion (H Λ : Subgroup G) : Prop :=
  let R := Λ ⊓ H
  let L := (pResidual 2 H).map H.subtype
  let D := R ⊓ centralizer (L : Set G)
  Common H Λ ∧
    ((∃ n, IsL2EvenBlock L n ∧ primeRank 2 D ≤ n ∧ PairFamily H Λ ∧ GlobalIndexTwo H Λ) ∨
     (IsAlternatingBlock L 3 ∧ primeRank 2 D ≤ 1 ∧ PairFamily H Λ ∧
       ((GlobalIndexTwo H Λ ∧ Nonempty (H ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) ∨
        (Nonempty (H ≃* Equiv.Perm (Fin 4)) ∧ (IsDihedralGroup Λ ∨ IsSemidihedralGroup Λ)))) ∨
     ((IsAlternatingBlock L 5 ∨ CubicPair L) ∧ FourFamily H Λ ∧
       elementaryAbelianMaxJ (Λ ⊓ normalizer (R : Set G)) = elementaryAbelianMaxJ R ∧
       (GlobalIndexTwo H Λ ∨ DihedralNormalizer H Λ)))
end CFSG.Quasithin.ChapterC.Section06.Original
