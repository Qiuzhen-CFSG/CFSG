module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.LocalReductions
public import CFSG.Quasithin.ClassicalModels

/-!
# The small-action reductions in characteristic two

This file records the literal subgroups used in 15.2.21--22.  In particular,

* `smallActionK` is the embedded `O²(H)`,
* `smallActionKc` is the `Mc`-orbit span of that subgroup, and
* `smallActionS` is the actual `C_T(ZS)`.

The action and model calculations which precede the two lemmas are retained as
explicit contracts.  They are not replaced by a tag saying that a subgroup is
in a particular family.  The first reduction packages the factorization and
the conjugate-factor conclusion of 15.2.21(1).  The second transports the
prime-to-three residual through the literal intersection `M ∩ Mc`, proving the
3'-group conclusion of 15.2.21(2).  The third and fourth reductions expose the
remaining model-exclusion and normal-closure inputs in 15.2.21(3) and 15.2.22.

The source's `N_I` and `M_I` are kept as the actual subgroup witnesses in the
case-(ii) record below.  No equality with an unrelated family member is
silently inferred.  The final model exclusion and normal-closure inputs are
owned by the small-parabolic and model branches; their consumers here use the
literal `K`, `Kc`, `S`, and relative normality conventions.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), Lemmas
15.2.21--22, printed pp.1114--1115; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06

variable {G : Type*} [Group G] [Finite G]

/-! ### The literal source subgroups and the quotient-action predicate -/

/-! The embedded two-residual `K = O²(H)`. -/
abbrev smallActionK (H : Subgroup G) : Subgroup G :=
  (pResidual 2 H).map H.subtype

/-! The literal `Mc`-orbit span `Kc = ⟨K^Mc⟩`. -/
abbrev smallActionKc (H Mc : Subgroup G) : Subgroup G :=
  conjugateSpanBy (smallActionK H) Mc

/-! The plane centralizer `S = C_T(ZS)`. -/
abbrev smallActionS (T : Sylow 2 G) (ZS : Subgroup G) : Subgroup G :=
  planeSylow T ZS

/-!
The subgroup-lattice form of the source phrase “`S` is irreducible on
`K/O₂(K)`”.  The first conjunct says that the action is defined on `K`; the
second says that the only `S`-invariant subgroups between the intrinsic
two-core and `K` are the endpoints.  All subgroups are subgroups of the
original ambient group `G`, so relative normality is visible in the statement.
-/
@[expose] def IsSmallActionIrreducible (S K : Subgroup G) : Prop :=
  S ≤ normalizer (K : Set G) ∧
    ∀ L : Subgroup G, K.pCoreIn 2 ≤ L → L ≤ K →
      S ≤ normalizer (L : Set G) → L = K.pCoreIn 2 ∨ L = K

/-! A literal 3'-group assertion, using the project's `O^{3'}` convention. -/
@[expose] def IsSmallActionThreePrime (X : Subgroup G) : Prop :=
  primeToResidual 3 X = ⊥

/-! ### The exact action clause used by 15.2.21(1) -/

/-!
The non-irreducible action calculation preceding 15.2.21(1).  `H₁,H₂` and
`K₁,K₂` are ambient subgroups, and the conjugation map is the actual ambient
map.  The `T − S` witness is represented by membership and non-membership,
not by an unconnected family label.
-/
structure SmallActionSplit (T S K : Subgroup G) where
  H₁ : Subgroup G
  H₂ : Subgroup G
  K₁ : Subgroup G
  K₂ : Subgroup G
  t : G
  t_mem : t ∈ T
  t_not_mem : t ∉ S
  K_sup_S : K ⊔ S = H₁ ⊔ H₂
  K₁_sup_K₂ : K₁ ⊔ K₂ = K
  K₁_le : K₁ ≤ K
  K₂_le : K₂ ≤ K
  K₁_conj : K₁.map (MulAut.conj t).toMonoidHom = K₂
  S_normalizes_K₁ : S ≤ normalizer (K₁ : Set G)
  S_normalizes_K₂ : S ≤ normalizer (K₂ : Set G)

/-! The literal output package for 15.2.21(1). -/
structure SmallAction21OneConclusion
    (T S K Kc ZS MI : Subgroup G) where
  split : SmallActionSplit T S K
  Kc_centralizes : Kc ≤ centralizer (ZS : Set G)
  Kc_eq_threePrime_MI : Kc = (primeToResidual 3 MI).map MI.subtype

/-! ### 15.2.21(1) -/

/-!
Original 15.2.21(1), with the earlier action calculation and the residual
identity supplied explicitly.  The conclusion is on the actual `K`, `Kc`,
`S`, and `M ∩ I`.
-/
def source_15_2_21_1
    {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (_d : PlaneUniquenessPreceding hsource H ZS)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H))
    (haction : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H) →
      SmallActionSplit (T : Subgroup G) (smallActionS T ZS) (smallActionK H))
    (hKc_centralizes : smallActionKc H Mc ≤ centralizer (ZS : Set G))
    (hKc_eq : smallActionKc H Mc =
      (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype) :
    SmallAction21OneConclusion (T : Subgroup G) (smallActionS T ZS)
      (smallActionK H) (smallActionKc H Mc) ZS (M ⊓ I) := by
  exact ⟨haction hnot, hKc_centralizes, hKc_eq⟩

/-! ### 15.2.21(2) -/

/-!
The residual-collapse input is the literal consequence of the earlier
15.2.8/15.2.12 clauses once `K = Kc`; it is phrased as an equality of the
embedded residual, so no quotient convention is hidden in the theorem below.
-/
theorem source_15_2_21_2
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hK_eq_Kc : smallActionK H = smallActionKc H Mc)
    (hcollapse : smallActionK H = smallActionKc H Mc →
      (primeToResidual 3 (M ⊓ Mc : Subgroup G)).map (M ⊓ Mc).subtype = ⊥) :
    IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)) := by
  let A : Subgroup G := M ⊓ Mc
  let C : Subgroup G := M ⊓ centralizer (V : Set G)
  have hCA : C ≤ A := by
    change C ≤ M ⊓ Mc
    rw [d.intersection]
    exact le_sup_left
  have hmap : (primeToResidual 3 C).map C.subtype = ⊥ := by
    have hm := embedded_primeToResidual_mono (p := 3) hCA
    have hm' : (primeToResidual 3 C).map C.subtype ≤ ⊥ := by
      simpa only [A, hcollapse hK_eq_Kc] using hm
    exact bot_unique hm'
  change primeToResidual 3 C = ⊥
  exact ((primeToResidual 3 C).map_eq_bot_iff_of_injective C.subtype_injective).mp hmap

/-! ### The exact case-(ii) data used by 15.2.21(3) and 15.2.22 -/

/-!
The source case-(ii) package.  `NI` and `Z₁` are the actual subgroup witnesses
from the source; `Y₁` is a genuine `O₂(Y₁)` subgroup, is `S`-invariant, has
the displayed `S₃` quotient, and is outside the literal `M_I = M ∩ I`.
-/
structure SmallActionCaseII (M I S : Subgroup G) where
  NI : Subgroup G
  Z₁ : Subgroup G
  Y₁ : Subgroup G
  Y₁_le_NI : Y₁ ≤ NI
  NI_eq_centralizer : NI = M ⊓ centralizer (Z₁ : Set G)
  NI_index_six : NI.relIndex M = 6
  Y₁_core : Y₁.pCoreIn 2 = Y₁
  S_normalizes_Y₁ : S ≤ normalizer (Y₁ : Set G)
  Y₁S_quotient_S3 :
    Nonempty (((Y₁ ⊔ S : Subgroup G) ⧸ pCore 2 (Y₁ ⊔ S : Subgroup G)) ≃*
      Equiv.Perm (Fin 3))
  Y₁_not_le_MI : ¬ Y₁ ≤ M ⊓ I

/-!
The remaining model exclusion in 15.2.21(3).  Its input is the concrete split
from 15.2.21(1), rather than the desired irreducibility conclusion itself.
The case-(ii) fields above remain available to the producer of this contract.
-/
structure SmallAction21ThreeData
    (T S K Kc M Mc I ZS : Subgroup G) where
  model_L4_2 : ClassicalGroup.IsPSL (Kc ⧸ pCore 2 Kc) 4 2
  case_ii : SmallActionCaseII M I S
  split_exclusion : ∀ (_hI : PlaneEscapes Mc ZS I)
      (_split : SmallActionSplit T S K), False

/-! ### 15.2.21(3) -/

/-! Original 15.2.21(3), retaining the literal L₄(2), case-(ii), and action
premises needed by the printed contradiction. -/
theorem source_15_2_21_3
    {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (_d : PlaneUniquenessPreceding hsource H ZS)
    (hI : PlaneEscapes Mc ZS I)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H))
    (haction : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H) →
      SmallActionSplit (T : Subgroup G) (smallActionS T ZS) (smallActionK H))
    (hdata : SmallAction21ThreeData (T : Subgroup G) (smallActionS T ZS)
      (smallActionK H) (smallActionKc H Mc) M Mc I ZS) :
    IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H) := by
  exact (hdata.split_exclusion hI (haction hnot)).elim

/-! ### 15.2.22 -/

/-!
The normal-closure data used in the proof of 15.2.22.  Under the assumed
commutator containment, the source construction produces the normalizer
containing the whole literal `K`; its source maximality bound puts that
normalizer in `M`.  This is the precise intermediate contradiction used below.
-/
structure SmallAction22Data
    (T S K M Mc I V H : Subgroup G) where
  fitting_eq : generalizedFitting I = pCore 2 I
  central_threePrime : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G))
  case_ii : SmallActionCaseII M I S
  split : SmallActionSplit T S K
  K_le_normalizer_of_commutator :
    ∀ (_hcomm : ⁅case_ii.Y₁, split.K₂⁆ ≤ case_ii.Y₁ ⊓ split.K₂),
      K ≤ normalizer
        ((case_ii.Y₁ ⊔ case_ii.Y₁.map (MulAut.conj split.t).toMonoidHom ⊔ T : Subgroup G) : Set G)
  normalizer_le_M :
    normalizer
        ((case_ii.Y₁ ⊔ case_ii.Y₁.map (MulAut.conj split.t).toMonoidHom ⊔ T : Subgroup G) : Set G) ≤ M

/-! The actual commutator conclusion, with relative normality and the source
`F*(I)=O₂(I)`/3'-centralizer assumptions retained in the input package. -/
theorem source_15_2_22
    {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : PlaneUniquenessPreceding hsource H ZS)
    (_hI : PlaneEscapes Mc ZS I)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H))
    (hdata : SmallAction22Data (T : Subgroup G) (smallActionS T ZS)
      (smallActionK H) M Mc I V H)
    (haction : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H) →
      SmallActionSplit (T : Subgroup G) (smallActionS T ZS) (smallActionK H))
    (_hsplit : hdata.split = haction hnot) :
    ¬ ⁅hdata.case_ii.Y₁, hdata.split.K₂⁆ ≤ hdata.case_ii.Y₁ ⊓ hdata.split.K₂ := by
  intro hcomm
  apply d.residual_not_le
  exact (hdata.K_le_normalizer_of_commutator hcomm).trans hdata.normalizer_le_M

end CFSG.Quasithin.Chapter15.Section02
