module

public import Theory.GroupTheory.FourWreathTwoCores
public import Theory.GroupTheory.NormalCharacteristicSection
public import Theory.GroupAction.FixedLineIndecomposability
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceCoreAction.WreathThompson
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceCoreAction.E16Actor
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceCoreAction.MarkedMovement
public import Theory.SpecificGroups.SymmetricFourSylow
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Core deductions in the actual Aut(M₁₂) wreath quotient

The intrinsic diagonal cubic calculation classifies a self-centralizing
invariant subgroup of `E₄ ≀ C₂`. These theorems lift that calculation along
the literal quotient map, retaining the specified quaternion base and other
abelian preimage. They do not assume that the quaternion core lies in the
unknown core. The compatible model and its action are explicit inputs.
The first two alternatives give relative normality of the quaternion core
by the characteristic wreath base. `source_core_alternatives` assembles these
with the actual quotient actor and the marked Thompson-normalizer movement.
In the elementary-sixteen branch the actor is `Mc/Q`, its action is literal
conjugation, and the actual whole-overlap quotient is dihedral of order eight.
In the normal-core branches a product of compatible residual cubics normalizes
the actual `J(T)` and moves the conjugate-generated source subgroup `V`.

This is a conditional source deduction. The parent must supply the compatible
wreath coordinates and first-parabolic action, the elementary preimage and its
S₄ quotient and fixed-center equation, and the compatible marked pair. The
first-parabolic wreath map and the marked Sylow swap embedding are distinct.
The latter has two-coset normal forms with `MarkedSylow.twist`, including
`swap ↦ z * swap`, and the four second-parabolic generator equations specified
in `MarkedMovement.CompatibleMarkedPair` and its `SecondGeometry` parent.
For a normal quaternion core the parent must also construct the two literal
binary-tetrahedral embeddings in `CompatibleResidualSwap`: they extend the
marked quaternion maps, commute, meet in the marked center, span mapped
`O²(Mc)`, and satisfy `swap_left`. An abstract residual central-product
isomorphism alone does not discharge these compatibility premises. None of
the trichotomy, actor recognition, indecomposability or movement conclusions
is an input, and this module does not itself complete source 14.2.21.

Source: Aschbacher--Smith, Lemma 14.2.21, printed p.988 (PDF p.1005).
-/

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceCoreAction

/-- The source trichotomy, conditional only on the compatible wreath
coordinates and the actual cubic invariance and self-centralizer condition.
The identifications name preimages of concrete subgroups, not core alternatives. -/
public theorem core_trichotomy_of_wreath
    {D : Type*} [Group D] (Z Q QK E : Subgroup D) [Z.Normal]
    (e : D ⧸ Z ≃* FourWreathTwo.Wreath)
    (hZQ : Z ≤ Q)
    (hQK : QK = FourWreathTwo.base.comap (e.toMonoidHom.comp (QuotientGroup.mk' Z)))
    (hE : E = FourWreathTwo.other.comap (e.toMonoidHom.comp (QuotientGroup.mk' Z)))
    (hcubic : ∀ w ∈ Q.map (e.toMonoidHom.comp (QuotientGroup.mk' Z)),
      FourWreathTwo.cubic w ∈ Q.map (e.toMonoidHom.comp (QuotientGroup.mk' Z)))
    (hcentral : Subgroup.centralizer
      (Q.map (e.toMonoidHom.comp (QuotientGroup.mk' Z)) : Set FourWreathTwo.Wreath) ≤
      Q.map (e.toMonoidHom.comp (QuotientGroup.mk' Z))) :
    Q = ⊤ ∨ Q = QK ∨ Q = E := by
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' Z)).ker = Z := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  simpa only [← hQK, ← hE] using
    FourWreathTwo.core_trichotomy_of_quotient
      (e.toMonoidHom.comp (QuotientGroup.mk' Z)) Q (hker.le.trans hZQ) hcubic hcentral

/-- The preimage of the other E₈ has order sixteen when the actual central
kernel has order two. The first equality computes its literal quotient. -/
public theorem other_core_card_of_wreath
    {D : Type*} [Group D] [Finite D] (Z E : Subgroup D) [Z.Normal]
    (e : D ⧸ Z ≃* FourWreathTwo.Wreath)
    (hZ : Nat.card Z = 2)
    (hE : E = FourWreathTwo.other.comap (e.toMonoidHom.comp (QuotientGroup.mk' Z))) :
    Nat.card (E ⧸ Z.subgroupOf E) = 8 ∧ Nat.card E = 16 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker : f.ker = Z := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hZQ : Z ≤ E := by
    calc
      Z = f.ker := hker.symm
      _ ≤ FourWreathTwo.other.comap f := Subgroup.ker_le_comap f _
      _ = E := hE.symm
  have hmap : E.map f = FourWreathTwo.other := by
    rw [hE, Subgroup.map_comap_eq_self_of_surjective hf]
  have hquot : Nat.card (E ⧸ Z.subgroupOf E) = 8 := by
    have h := Subgroup.relIndex_ker E f
    rw [hker, hmap, FourWreathTwo.card_other] at h
    exact h
  have hmul := (Z.subgroupOf E).card_mul_index
  have hZ' : Nat.card (Z.subgroupOf E) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv).trans hZ
  rw [Subgroup.index_eq_card, hquot, hZ'] at hmul
  exact ⟨hquot, by omega⟩

/-- Restrict the source centralizer chain in `Mc/Z` to the actual `QH/Z`
coordinates. The ambient group `D` here is `Mc`, not the global simple group. -/
public theorem self_centralizing_of_source_chain
    {D : Type*} [Group D] (Z Q QH : Subgroup D) [Z.Normal]
    (hQQH : Q ≤ QH) (f : QH →* FourWreathTwo.Wreath)
    (hf : Function.Surjective f) (hker : f.ker = Z.subgroupOf QH)
    (hchain : Subgroup.centralizer
      (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) ≤
        Q.map (QuotientGroup.mk' Z)) :
    Subgroup.centralizer ((Q.subgroupOf QH).map f : Set FourWreathTwo.Wreath) ≤
      (Q.subgroupOf QH).map f := by
  let π := (QuotientGroup.mk' Z).comp QH.subtype
  have hπker : π.ker = Z.subgroupOf QH := by
    ext x
    change (QuotientGroup.mk' Z) (x : D) = 1 ↔ (x : D) ∈ Z
    exact QuotientGroup.eq_one_iff _
  have heq (a b : QH) : f a = f b ↔ π a = π b := by
    rw [f.eq_iff, π.eq_iff, hker, hπker]
  intro w hw
  obtain ⟨x, rfl⟩ := hf w
  have hxc : π x ∈ Subgroup.centralizer
      (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) := by
    rintro y ⟨q, hq, rfl⟩
    let q' : QH := ⟨q, hQQH hq⟩
    have hcomm := hw (f q') ⟨q', hq, rfl⟩
    have hfcomm : f (q' * x) = f (x * q') := by
      simpa only [map_mul] using hcomm
    have hπcomm := (heq (q' * x) (x * q')).mp hfcomm
    change π q' * π x = π x * π q'
    simpa only [map_mul] using hπcomm
  obtain ⟨q, hq, hqx⟩ := hchain hxc
  let q' : QH := ⟨q, hQQH hq⟩
  exact ⟨q', hq, (heq q' x).mpr hqx⟩

/-- The invariant-core trichotomy in `Mc`, using the actual conjugation
by a local cubic and the literal centralizer chain in `Mc/Z`.
All normality assumptions are internal to `Mc`. The displayed quotient
coordinates are the permitted base-model input. -/
public theorem core_trichotomy_in_larger_local
    {D : Type*} [Group D] (Z Q QH QK A : Subgroup D)
    [Z.Normal] [Q.Normal] (hZQ : Z ≤ Q) (hQQH : Q ≤ QH)
    (f : QH →* FourWreathTwo.Wreath)
    (hf : Function.Surjective f) (hker : f.ker = Z.subgroupOf QH)
    (hQK : QK = (FourWreathTwo.base.comap f).map QH.subtype)
    (hA : A = (FourWreathTwo.other.comap f).map QH.subtype)
    (h : D) (hn : h ∈ Subgroup.normalizer (QH : Set D))
    (hact : ∀ x : QH,
      f ⟨h * (x : D) * h⁻¹, (hn (x : D)).mp x.property⟩ =
        FourWreathTwo.cubic (f x))
    (hchain : Subgroup.centralizer
      (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) ≤
        Q.map (QuotientGroup.mk' Z)) :
    Q = QH ∨ Q = QK ∨ Q = A := by
  have hcubic : ∀ w ∈ (Q.subgroupOf QH).map f,
      FourWreathTwo.cubic w ∈ (Q.subgroupOf QH).map f := by
    rintro w ⟨x, hx, rfl⟩
    refine ⟨⟨h * (x : D) * h⁻¹, (hn (x : D)).mp x.property⟩, ?_, hact x⟩
    exact Subgroup.Normal.conj_mem inferInstance (x : D) hx h
  have hk : f.ker ≤ Q.subgroupOf QH := by
    rw [hker]
    intro x hx
    exact hZQ hx
  have hrecover := Subgroup.map_subgroupOf_eq_of_le hQQH
  obtain he | he | he := FourWreathTwo.core_trichotomy_of_quotient
    f (Q.subgroupOf QH) hk hcubic
    (self_centralizing_of_source_chain Z Q QH hQQH f hf hker hchain)
  · left
    exact le_antisymm hQQH (Subgroup.subgroupOf_eq_top.mp he)
  · right; left
    rw [← hrecover, he, ← hQK]
  · right; right
    rw [← hrecover, he, ← hA]

/-- The first two core alternatives also make the quaternion core normal
in `Mc`. Normality is obtained from the characteristic wreath base and the
actual normal marked kernel, without assuming `QK ≤ Q` in the third branch. -/
public theorem core_trichotomy_with_relative_normality
    {D : Type*} [Group D] (Z Q QH QK A : Subgroup D)
    [Z.Normal] [Q.Normal] (hZQ : Z ≤ Q) (hQQH : Q ≤ QH)
    (f : QH →* FourWreathTwo.Wreath)
    (hf : Function.Surjective f) (hker : f.ker = Z.subgroupOf QH)
    (hQK : QK = (FourWreathTwo.base.comap f).map QH.subtype)
    (hA : A = (FourWreathTwo.other.comap f).map QH.subtype)
    (h : D) (hn : h ∈ Subgroup.normalizer (QH : Set D))
    (hact : ∀ x : QH,
      f ⟨h * (x : D) * h⁻¹, (hn (x : D)).mp x.property⟩ =
        FourWreathTwo.cubic (f x))
    (hchain : Subgroup.centralizer
      (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) ≤
        Q.map (QuotientGroup.mk' Z)) :
    (Q = QH ∧ QK.Normal) ∨ (Q = QK ∧ QK.Normal) ∨ Q = A := by
  let e : QH ⧸ Z.subgroupOf QH ≃* FourWreathTwo.Wreath :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he : e.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf QH)) = f := by
    apply MonoidHom.ext
    intro x
    rfl
  have hnormal (hQH : QH.Normal) : QK.Normal := by
    let : QH.Normal := hQH
    apply Subgroup.normal_preimage_characteristic_quotient Z QH QK e FourWreathTwo.base
    rwa [he]
  obtain hwhole | hbase | hother := core_trichotomy_in_larger_local
    Z Q QH QK A hZQ hQQH f hf hker hQK hA h hn hact hchain
  · exact Or.inl ⟨hwhole, hnormal (hwhole ▸ inferInstance)⟩
  · exact Or.inr (Or.inl ⟨hbase, hbase ▸ inferInstance⟩)
  · exact Or.inr (Or.inr hother)

open Subgroup
open scoped IsMulCommutative

/-- Cardinality of the other lifted core in the actual larger local group. -/
public theorem other_core_card_in_larger_local
    {D : Type*} [Group D] [Finite D] (Z QH A : Subgroup D) [Z.Normal]
    (hZ : Nat.card Z = 2) (hZQH : Z ≤ QH)
    (f : QH →* FourWreathTwo.Wreath) (hf : Function.Surjective f)
    (hker : f.ker = Z.subgroupOf QH)
    (hA : A = (FourWreathTwo.other.comap f).map QH.subtype) :
    Nat.card A = 16 := by
  let e : QH ⧸ Z.subgroupOf QH ≃* FourWreathTwo.Wreath :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he : e.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf QH)) = f := by
    apply MonoidHom.ext
    intro x
    rfl
  have hZ' : Nat.card (Z.subgroupOf QH) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZQH).toEquiv).trans hZ
  have hcard := (other_core_card_of_wreath (Z.subgroupOf QH)
    (FourWreathTwo.other.comap f) e hZ' (by rw [he])).2
  rw [hA, card_map_of_injective QH.subtype_injective]
  exact hcard

/-- The characteristic wreath base is the actual Thompson subgroup of
`QH/Z`, with both sides transported through the specified quotient map. -/
public theorem wreath_thompson_in_larger_local
    {D : Type*} [Group D] (Z QH QK : Subgroup D) [Z.Normal]
    (f : QH →* FourWreathTwo.Wreath) (hf : Function.Surjective f)
    (hker : f.ker = Z.subgroupOf QH)
    (hQK : QK = (FourWreathTwo.base.comap f).map QH.subtype) :
    Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup (QH ⧸ Z.subgroupOf QH)) =
      (QK.subgroupOf QH).map (QuotientGroup.mk' (Z.subgroupOf QH)) := by
  let e : QH ⧸ Z.subgroupOf QH ≃* FourWreathTwo.Wreath :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he : e.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf QH)) = f := by
    apply MonoidHom.ext
    intro x
    rfl
  apply FourWreathTwo.elementary_thompson_quotient_eq_base_image
    (Z.subgroupOf QH) (QK.subgroupOf QH) e
  rw [he, hQK]
  exact comap_map_eq_self_of_injective QH.subtype_injective _

private theorem overlap_sylow_dihedral
    {D : Type*} [Group D] [Finite D] (Q H : Subgroup D) [Q.Normal]
    (eH : (H ⧸ Q.subgroupOf H) ≃* Equiv.Perm (Fin 4))
    (T : Sylow 2 D) (hTH : (T : Subgroup D) ≤ H) :
    Nonempty ((T.mapSurjective (QuotientGroup.mk'_surjective Q)) ≃* DihedralGroup 4) := by
  let S := T.mapSurjective (QuotientGroup.mk'_surjective Q)
  have hSH : (S : Subgroup (D ⧸ Q)) ≤ H.map (QuotientGroup.mk' Q) := map_mono hTH
  let R := S.subtype hSH
  let e := (E16Actor.overlapQuotientEquiv Q H).symm.trans eH
  let P := R.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨eP⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four P
  exact ⟨(subgroupOfEquivOfLe hSH).symm.trans
    (((R : Subgroup (H.map (QuotientGroup.mk' Q))).equivMapOfInjective
      e.toMonoidHom e.injective).trans eP)⟩

/-- The E₁₆ conclusion uses the actual quotient and its literal conjugation
representation. `U` is the actual whole-overlap Sylow subgroup inside `D`.
This predicate is an output of the assembly, never a model premise. -/
@[expose] public def E16ConjugationAlternative
    {D : Type*} [Group D] (Q Z H U : Subgroup D) [Q.Normal]
    [IsElementaryAbelian 2 Q] : Prop :=
  Nonempty ((D ⧸ Q) ≃* Matrix.PSL3Two.PSL) ∧
  Nonempty (Q ≃* Multiplicative (Fin 4 → ZMod 2)) ∧
  Function.Injective (E16Actor.conjugation Q) ∧
  Function.Injective (E16Actor.binaryAction Q) ∧
  Module.finrank (ZMod 2) (Additive Q) = 4 ∧
  (∃ z : Q, (z : D) ∈ Z ∧ z ≠ 1 ∧ zpowers z = Z.subgroupOf Q ∧
    ∀ a : D ⧸ Q, E16Actor.binaryAction Q a (Additive.ofMul z) = Additive.ofMul z) ∧
  (∀ R S : Submodule (ZMod 2) (Additive Q),
    (∀ a : D ⧸ Q, ∀ r ∈ R, E16Actor.binaryAction Q a r ∈ R) →
    (∀ a : D ⧸ Q, ∀ s ∈ S, E16Actor.binaryAction Q a s ∈ S) →
    Disjoint R S → R = ⊥ ∨ S = ⊥) ∧
  (∀ d : D, ∀ q : Q,
    ((E16Actor.conjugation Q) (QuotientGroup.mk' Q d) q : D) = d * (q : D) * d⁻¹) ∧
  (∀ d : D, ∀ q : Q,
    E16Actor.binaryAction Q (QuotientGroup.mk' Q d) (Additive.ofMul q) =
      Additive.ofMul (MulAut.conjNormal d q)) ∧
  Nat.card (D ⧸ Q) = 168 ∧
  Nat.card (H.map (QuotientGroup.mk' Q)) = 24 ∧
  (H.map (QuotientGroup.mk' Q)).index = 7 ∧ H.index = 7 ∧
  Q ≤ U ∧ Nonempty ((U ⧸ Q.subgroupOf U) ≃* DihedralGroup 4) ∧
  ∃ S : Sylow 2 (D ⧸ Q), (S : Subgroup (D ⧸ Q)) = U.map (QuotientGroup.mk' Q) ∧
    Nat.card S = 8 ∧ Nonempty (S ≃* DihedralGroup 4) ∧
    (S : Subgroup (D ⧸ Q)) ≤ H.map (QuotientGroup.mk' Q)

/-- The movement conclusion keeps the actual Thompson subgroup, relative
normality in the second parabolic, and membership in the mapped residual.
The final clause is precisely the source normalizer obstruction. -/
@[expose] public def MarkedThompsonMovement
    {G : Type*} [Group G] (Mc : Subgroup G) (T : Sylow 2 G)
    (YT V : Subgroup G) : Prop :=
  Nonempty (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≃*
    QuaternionSwapModel.E16) ∧
  Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ YT ∧
  ((Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf YT).Normal ∧
  (∃ g : ((pResidual 2 Mc).map Mc.subtype ⊓
      normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G)
      : Subgroup G), V.map (MulAut.conj (g : G)).toMonoidHom ≠ V) ∧
  ¬ normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤
    normalizer (V : Set G)

/-- Assemble the source core alternatives in the ambient type `Mc`.
The wreath quotient map `f` describes the first-parabolic two-core. The
separate map `swap` describes an order-64 subgroup of the whole Sylow; no
identification of its image with that first two-core is made.

The model owner must supply the wreath coordinates and cubic conjugation,
elementarity of the other preimage, its S₄ quotient and fixed-center equation,
and the literal marked-pair equations. In the two normal-core cases it must
also supply compatible residual embeddings including `swap_left`. An abstract
quaternion residual central product alone does not supply those embeddings.
All recognition, indecomposability, Thompson and movement assertions below
are proved conclusions. This conditional assembly does not discharge the
source model or complete 14.2.21. -/
public theorem source_core_alternatives
    {G : Type*} [Group G] [Finite G] (Mc : Subgroup G) (H : Subgroup Mc)
    (Z Q QH QK A : Subgroup Mc) [Z.Normal] [Q.Normal]
    [IsElementaryAbelian 2 A] [(A.subgroupOf H).Normal]
    (hQ : Q = pCore 2 Mc) (hQH : QH = (pCore 2 H).map H.subtype)
    (hQKcomm : QK = ⁅QH, (pResidual 2 H).map H.subtype⁆)
    (hZ : Nat.card Z = 2) (hZQ : Z ≤ Q) (hQQH : Q ≤ QH)
    (f : QH →* FourWreathTwo.Wreath) (hf : Function.Surjective f)
    (hker : f.ker = Z.subgroupOf QH)
    (hQK : QK = (FourWreathTwo.base.comap f).map QH.subtype)
    (hA : A = (FourWreathTwo.other.comap f).map QH.subtype)
    (h : H) (hn : (h : Mc) ∈ normalizer (QH : Set Mc))
    (hact : ∀ x : QH,
      f ⟨(h : Mc) * (x : Mc) * (h : Mc)⁻¹, (hn (x : Mc)).mp x.property⟩ =
        FourWreathTwo.cubic (f x))
    (hchain : centralizer
      (Q.map (QuotientGroup.mk' Z) : Set (Mc ⧸ Z)) ≤ Q.map (QuotientGroup.mk' Z))
    (eH : (H ⧸ A.subgroupOf H) ≃* Equiv.Perm (Fin 4))
    (hcentral : A ⊓ centralizer (QK : Set Mc) = Z)
    (hstrict : (pResidual 2 H).map H.subtype < pResidual 2 Mc)
    (swap : QuaternionSwapModel.QH →* G) (T : Sylow 2 G) (YT V B C : Subgroup G)
    (pair : MarkedMovement.CompatibleMarkedPair swap T (H.map Mc.subtype) YT
      (Z.map Mc.subtype) V (QK.map Mc.subtype) B C)
    (residual : QK.Normal → Nonempty
      (MarkedMovement.CompatibleResidualSwap swap ((pResidual 2 Mc).map Mc.subtype))) :
    (Q = QH ∧ QK.Normal ∧
      Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup (QH ⧸ Z.subgroupOf QH)) =
        (QK.subgroupOf QH).map (QuotientGroup.mk' (Z.subgroupOf QH)) ∧
      MarkedThompsonMovement Mc T YT V) ∨
    (Q = QK ∧ QK.Normal ∧ MarkedThompsonMovement Mc T YT V) ∨
    (Q = A ∧ ∃ hE : IsElementaryAbelian 2 Q,
      letI := hE
      E16ConjugationAlternative Q Z H ((T : Subgroup G).subgroupOf Mc)) := by
  have hQHH : QH ≤ H := by
    rw [hQH]
    exact map_subtype_le _
  have htwo : IsPGroup 2 QH := by
    rw [hQH]
    exact pCore_isPGroup.map H.subtype
  have hHN : H ≤ normalizer (QH : Set Mc) := by
    rw [hQH]
    intro x hx
    apply (pCore 2 H).le_normalizer_map H.subtype
    exact ⟨⟨x, hx⟩, by rw [normalizer_eq_top]; trivial, rfl⟩
  have hQKtwo : IsPGroup 2 QK := htwo.to_le (by
    rw [hQKcomm]
    exact le_normalizer_iff_commutator_le_left.mp ((map_subtype_le _).trans hHN))
  have hmove (hnormal : QK.Normal) : MarkedThompsonMovement Mc T YT V := by
    obtain ⟨r⟩ := residual hnormal
    obtain ⟨_, hE, hJ, hN, hm⟩ :=
      MarkedMovement.marked_thompson_normalizer_movement Mc pair r
    refine ⟨hE, hJ, hN, hm, ?_⟩
    intro hcontrol
    obtain ⟨g, hg⟩ := hm
    exact hg (mem_normalizer_iff_map_conj_eq.mp (hcontrol g.property.2))
  obtain hwhole | hbase | hother := core_trichotomy_with_relative_normality
    Z Q QH QK A hZQ hQQH f hf hker hQK hA (h : Mc) hn hact hchain
  · exact Or.inl ⟨hwhole.1, hwhole.2,
      wreath_thompson_in_larger_local Z QH QK f hf hker hQK, hmove hwhole.2⟩
  · exact Or.inr (Or.inl ⟨hbase.1, hbase.2, hmove hbase.2⟩)
  · refine Or.inr (Or.inr ⟨hother, ?_⟩)
    cases hother
    refine ⟨inferInstance, ?_⟩
    have hcard := other_core_card_in_larger_local Z QH Q hZ (hZQ.trans hQQH) f hf hker hA
    obtain ⟨hL, hE, hfaith, hbfaith, hdim, hfix, hind⟩ :=
      E16Actor.larger_actor Q Z hQ hcard hZ hZQ hchain H (hQQH.trans hQHH)
        eH hstrict QK hQKtwo hcentral
    obtain ⟨hactor, hoverlap, hindex, hHindex⟩ :=
      E16Actor.actor_card_and_overlap_index Q Z hZ hZQ hQ hcard hchain H
        (hQQH.trans hQHH) eH hstrict
    refine ⟨hL, hE, hfaith, hbfaith, hdim, hfix, hind,
      E16Actor.conjugation_apply Q, E16Actor.binaryAction_apply Q,
      hactor, hoverlap, hindex, hHindex, ?_⟩
    have hTH : (T : Subgroup G) ≤ H.map Mc.subtype := pair.whole_overlap.ge.trans inf_le_left
    have hTMc : (T : Subgroup G) ≤ Mc := hTH.trans (map_subtype_le _)
    let S : Sylow 2 Mc := T.subtype hTMc
    have hSH : (S : Subgroup Mc) ≤ H := by
      intro x hx
      obtain ⟨y, hy, he⟩ := hTH hx
      exact Mc.subtype_injective he ▸ hy
    obtain ⟨hS, hSH'⟩ := E16Actor.whole_overlap_sylow Q Z hZ hZQ hQ hcard hchain
      H (hQQH.trans hQHH) eH hstrict S hSH
    obtain ⟨eS⟩ := overlap_sylow_dihedral Q H eH S hSH
    have hQS : Q ≤ (S : Subgroup Mc) := by
      rw [hQ]
      exact pCore_isPGroup.le_sylow_of_normal S
    exact ⟨hQS, ⟨(E16Actor.overlapQuotientEquiv Q (S : Subgroup Mc)).trans eS⟩,
      S.mapSurjective (QuotientGroup.mk'_surjective Q), rfl, hS, ⟨eS⟩, hSH'⟩


end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceCoreAction
