module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.Placement
public import Theory.Representation.BinaryConjugationSection.SubspacePreimages
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# Literal supports of the terminal homogeneous seeds

Inflate the faithful U/Z action from H/O₂(H) to H and take the full
coordinate preimage of a homogeneous Irr⁺ member. The result is an actual
subgroup W of U, contains the original central line, and lies in
[U,⟨K^T⟩]. Its original normalizer is exactly the subspace stabilizer.
Distinct Sylow conjugates overlap in the centralizer of the perfect
component orbit. The hatted orbit decomposition is transported to this
literal support span, with its independence and nonisomorphism retained.

At H=Mc the source hypotheses construct these supports unconditionally.
For relatively normal K, the final consumer discharges fitting placement,
normalization and separated conjugates in U0--U3. The remaining index-two,
local-normalizer and fixed-moving inputs, as well as natural recognition,
FF elimination and full orbit exhaustion, stay with
qt-e-suitable-component-supports. The source input 14.6.18 stays with
qt-e-14625-source. No fixed-free hypothesis on the A6 cover is used.

Source: Aschbacher--Smith A.1.40--42, F.9.18 and 14.6.22--24,
printed pp.31--32,325--326,1038--1039.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
variable {G : Type*} [Group G]

/-- The original quotient coordinates, with the actor inflated back to H. -/
@[expose] def originalSection {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) :
    BinaryConjugationSection H U Z
      (a.representation.comp (QuotientGroup.mk' (pCore 2 H))) where
  section_le := a.le_local
  kernel_le := a.kernel_le
  normalized := a.normalizes
  coordinates := (MulEquiv.multiplicativeAdditive (U ⧸ Z.subgroupOf U)).symm.toMonoidHom.comp
    (QuotientGroup.mk' (Z.subgroupOf U))
  onto := (MulEquiv.multiplicativeAdditive _).symm.surjective.comp
    (QuotientGroup.mk'_surjective _)
  kernel_eq := by ext u; exact QuotientGroup.eq_one_iff u
  equivariant h u := (a.conjugation h u).symm

/-- Inflation retains the same subspace and the literal original actor. -/
theorem originalSection_irrPlus {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (K : Subgroup G)
    {I : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U))}
    (hI : IsIrrPlus a.representation (actorImage H K) I) :
    IsIrrPlus (a.representation.comp (QuotientGroup.mk' (pCore 2 H)))
      (K.subgroupOf H) I := by
  simpa only [Submodule.map_id] using
    IsIrrPlus.map_embedding
      (a.representation.comp (QuotientGroup.mk' (pCore 2 H))) a.representation
      (QuotientGroup.mk' (pCore 2 H)) (LinearMap.id) Function.injective_id
      (fun _ _ => rfl) (K.subgroupOf H) I hI

/-- Taking the original ambient conjugate span agrees with the orbit span
under the literal image in H/O₂(H). -/
theorem originalSection_support_orbit {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (A : Subgroup G) (hAH : A ≤ H)
    (I : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U))) :
    (originalSection a).imageSpace
      (conjugateSpanBy ((originalSection a).subspacePreimage I) A) =
      orbitSpan a.representation (actorImage H A) I := by
  let c := originalSection a
  let W := c.subspacePreimage I
  let q := QuotientGroup.mk' (pCore 2 H)
  have hWU : W ≤ U := c.subspacePreimage_le I
  have he (t : A) :
      c.imageSpace (W.map (MulAut.conj (t:G)).toMonoidHom) =
        I.map (a.representation (q ⟨t,hAH t.property⟩)) := by
    change c.imageSpace (W.conjBy (t:G)) = _
    rw [c.imageSpace_conjBy W hWU ⟨t,hAH t.property⟩,c.imageSpace_subspacePreimage]
    rfl
  change c.imageSpace (conjugateSpanBy W A) = _
  rw [conjugateSpanBy_eq_iSup_conj,c.imageSpace_iSup]
  · apply le_antisymm
    · apply iSup_le
      intro t
      rw [he]
      exact le_iSup (fun t : actorImage H A => I.map (a.representation t))
        ⟨q ⟨t,hAH t.property⟩,⟨⟨t,hAH t.property⟩,t.property,rfl⟩⟩
    · apply iSup_le
      rintro ⟨_,t,ht,rfl⟩
      have hh := le_iSup
        (fun t : A => c.imageSpace (W.map (MulAut.conj (t:G)).toMonoidHom)) ⟨t,ht⟩
      rwa [he] at hh
  · intro t x hx
    obtain ⟨w,hw,rfl⟩ := hx
    exact (mem_normalizer_iff.mp (a.normalizes (hAH t.property)) w).mp (hWU hw)

/-- The hatted homogeneous decomposition is the decomposition of the
literal lifted support orbit. This identifies the original span without
asserting that it exhausts all of [U,X]. -/
theorem originalSection_hatted_support_decomposition
    {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (X A : Subgroup G) (hAH : A ≤ H)
    {I : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U))}
    (hI : IsIrrPlusWith a.representation (actorImage H X) (actorImage H A) I) :
    let Ω := centralOrbit a.representation (actorImage H X) (actorImage H A)
      hI.normalizes (quotientImage a.representation (actorImage H X) I hI.invariant)
    iSupIndep (fun B : Ω => B.val.toSubmodule) ∧
      (⨆ B : Ω, B.val.toSubmodule) =
        ((originalSection a).imageSpace
          (conjugateSpanBy ((originalSection a).subspacePreimage I) A)).map
          (fixedSpace a.representation (actorImage H X)).mkQ ∧
      ∀ B C : Ω, B ≠ C → ¬ SameModule B.val C.val := by
  rw [originalSection_support_orbit a A hAH I]
  exact hI.orbit_decomposition a.representation

/-- Exhaustion of the coordinate commutator lifts to equality of the
original commutator with the conjugate span of the actual support. -/
theorem originalSection_commutator_eq_support_span
    {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (X A : Subgroup G) (hXH : X ≤ H) (hAH : A ≤ H)
    (I : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)))
    (hZ : Z ≤ ⁅U,X⁆)
    (hexhaust : (originalSection a).imageSpace ⁅U,X⁆ =
      orbitSpan a.representation (actorImage H A) I) :
    ⁅U,X⁆ = conjugateSpanBy ((originalSection a).subspacePreimage I) A := by
  let c := originalSection a
  have hleft : ⁅U,X⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp (hXH.trans a.normalizes)
  have hright : conjugateSpanBy (c.subspacePreimage I) A ≤ U :=
    conjugateSpanBy_le (c.subspacePreimage_le I) (hAH.trans a.normalizes)
  have hrightZ : Z ≤ conjugateSpanBy (c.subspacePreimage I) A :=
    (c.kernel_le_subspacePreimage I).trans (le_conjugateSpanBy _ A)
  rw [←c.subspacePreimage_imageSpace ⁅U,X⁆ hleft hZ,
    ←c.subspacePreimage_imageSpace (conjugateSpanBy (c.subspacePreimage I) A) hright hrightZ]
  congr 1
  exact hexhaust.trans (originalSection_support_orbit a A hAH I).symm

variable [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv

/-- A genuine homogeneous seed lifts to an original support in [U,⟨K^T⟩].
Its distinct Sylow conjugates have component-central overlap. -/
theorem source_lifted_seed_support
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H)))}
    (hI : IsIrrPlusWith a.representation
      (componentOrbit (actorImage H K) (quotientSylow H T hH.1.2))
      (quotientSylow H T hH.1.2) I) :
    let X := conjugateSpanBy K (T : Subgroup G)
    let c := originalSection a
    let W := c.subspacePreimage I
    centralInvolutions T ≤ W ∧
      W ≤ ⁅conjugateSpanBy (localModule T M) H,X⁆ ∧
      X ≤ normalizer (W : Set G) ∧
      (∀ h : H, (h:G) ∈ normalizer (W : Set G) ↔
        I.map (a.representation (QuotientGroup.mk' (pCore 2 H) h)) = I) ∧
      ∀ t ∈ (T : Subgroup G), t ∉ (T : Subgroup G) ⊓ normalizer (W : Set G) →
        W ⊓ W.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer (X : Set G) ∧
        X ≤ normalizer (W.map (MulAut.conj t⁻¹).toMonoidHom : Set G) := by
  let X := conjugateSpanBy K (T : Subgroup G)
  let c := originalSection a
  let W := c.subspacePreimage I
  have hXH : X ≤ H := conjugateSpanBy_le hKH (hH.1.2.trans H.le_normalizer)
  have hIq : IsIrrPlus a.representation (actorImage H X) I := by
    simpa only [quotient_componentOrbit H K T hKH hH.1.2] using hI.isIrrPlus
  have hi := originalSection_irrPlus a X hIq
  have hz : centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) H,X⁆ :=
    (source_component_support_placement hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK).1.trans (commutator_mono le_rfl (le_conjugateSpanBy K _))
  let : Group.IsPerfect (K.subgroupOf H) := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  let : Group.IsPerfect X := conjugateSpanBy_isPerfect K (T : Subgroup G)
  have h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hZX : centralInvolutions T ≤ centralizer (X : Set G) :=
    (le_centralizer_iff.mp h.H_centralizes).trans (centralizer_le hXH)
  refine ⟨c.kernel_le_subspacePreimage I,c.irrPlus_preimage_le_commutator X hXH hz hi,
    c.subspacePreimage_normalized X hXH I hi.choose,
    fun h => c.mem_normalizer_subspacePreimage_iff I h,?_⟩
  intro t ht hn
  have hinv : t⁻¹ ∉ normalizer (W : Set G) := by
    intro hx
    exact hn ⟨ht,(normalizer (W : Set G)).inv_mem_iff.mp hx⟩
  exact c.irrPlus_preimage_separated X hXH hZX hi
    ⟨t⁻¹,hH.1.2 ((T : Subgroup G).inv_mem ht)⟩
    ((source_component_orbit_normal hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK) (hH.1.2 ((T : Subgroup G).inv_mem ht))) hinv

/-- The original terminal U/Z has an actual lifted homogeneous support,
with the exact normalizer and all distinct conjugate separations. -/
theorem terminal_exists_lifted_seed_support
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T),
      ∃ I,
        IsIrrPlusWith a.representation
          (componentOrbit (actorImage Mc K) (quotientSylow Mc T
            (terminal_outside hG T hempty hM hunique hmany hcard e).1.2))
          (quotientSylow Mc T (terminal_outside hG T hempty hM hunique hmany hcard e).1.2) I ∧
        let X := conjugateSpanBy K (T : Subgroup G)
        let c := originalSection a
        let W := c.subspacePreimage I
        centralInvolutions T ≤ W ∧ W ≤ ⁅conjugateSpanBy (localModule T M) Mc,X⁆ ∧
          X ≤ normalizer (W : Set G) ∧
          (∀ h : Mc, (h:G) ∈ normalizer (W : Set G) ↔
            I.map (a.representation (QuotientGroup.mk' (pCore 2 Mc) h)) = I) ∧
          ∀ t ∈ (T : Subgroup G), t ∉ (T : Subgroup G) ⊓ normalizer (W : Set G) →
            W ⊓ W.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer (X : Set G) ∧
            X ≤ normalizer (W.map (MulAut.conj t⁻¹).toMonoidHom : Set G) := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨hU,a,I,hI,_⟩ := terminal_component_seed_inputs
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK
  let := hU
  exact ⟨hU,a,I,hI,source_lifted_seed_support
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK a hI⟩

/-- For a relatively normal component, a fixed-moving vector in the lifted
seed gives U0--U3 with S equal to its literal Sylow normalizer. The support
separation and fitting placement are proved here. Index two, the local
normalizer and the marked fixed-moving vector remain with this source owner. -/
theorem source_exists_on_normal_seed
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hnK : (K.subgroupOf Mc).Normal)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc)))}
    (hI : IsIrrPlusWith a.representation
      (componentOrbit (actorImage Mc K) (quotientSylow Mc T
        (terminal_outside hG T hempty hM hunique hmany hcard e).1.2))
      (quotientSylow Mc T (terminal_outside hG T hempty hM hunique hmany hcard e).1.2) I)
    (hindex : ((T : Subgroup G) ⊓ normalizer ((originalSection a).subspacePreimage I : Set G)).relIndex
      (T : Subgroup G) = 2)
    (hlocal : Mc ⊓ normalizer (((T : Subgroup G) ⊓
      normalizer ((originalSection a).subspacePreimage I : Set G) : Subgroup G) : Set G) =
      (T : Subgroup G))
    (v : Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc)))
    (hv : v ∈ I)
    (hfixed : ∀ (s : Mc), (s:G) ∈ (T : Subgroup G) ⊓
      normalizer ((originalSection a).subspacePreimage I : Set G) →
      a.representation (QuotientGroup.mk' (pCore 2 Mc) s) v = v)
    (hmoved : v ∉ fixedSpace
      (a.representation.comp (QuotientGroup.mk' (pCore 2 Mc))) (K.subgroupOf Mc)) :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    let W := (originalSection a).subspacePreimage I
    ∃ u ∈ W, u ^ 2 = 1 ∧ u ≠ 1 ∧
      suitableQuotientCentralizer h u = (T : Subgroup G) ⊓ normalizer (W : Set G) ∧
      Suitable h Mc u := by
  let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  let c := originalSection a
  let W := c.subspacePreimage I
  let S := (T : Subgroup G) ⊓ normalizer (W : Set G)
  have hX : conjugateSpanBy K (T : Subgroup G) = K :=
    le_antisymm (conjugateSpanBy_le le_rfl (hout.1.2.trans
      ((normal_subgroupOf_iff_le_normalizer hKM).mp hnK))) (le_conjugateSpanBy K _)
  have hs := source_lifted_seed_support hG T hempty hM hunique hmany hcard e hab hsolv
    Mc hout K hKM hK a hI
  dsimp only at hs
  rw [hX] at hs
  obtain ⟨hz,hle,hn,_,hsep⟩ := hs
  have hWU : W ≤ conjugateSpanBy (localModule T M) Mc := c.subspacePreimage_le I
  have hSM : S ≤ Mc := inf_le_left.trans hout.1.2
  obtain ⟨u,hu,huf,hum⟩ := c.exists_fixed_moving_subspace_lift I K S hSM v hv
    (fun s hs => hfixed ⟨s,hSM hs⟩ hs) hmoved
  let : Group.IsPerfect (K.subgroupOf Mc) := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKM).toMonoidHom) (subgroupOfEquivOfLe hKM).surjective
  obtain ⟨heq,hm,hp,hl⟩ := source_suitable_of_central_overlap
    hG T hempty hM hunique hmany hcard e hab Mc hout K W S
    (source_component_fitting_placement hG T hempty hM hunique hmany hcard e hab hsolv
      Mc hout K hKM hK) hWU hz hn inf_le_left hindex hlocal hsep u hu huf hum
  have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) u (hWU hu)
  have hune : u ≠ 1 := by
    rintro rfl
    obtain ⟨k,_,hk⟩ := hum
    exact hk (by simp)
  refine ⟨u,hu,hu2,hune,heq,hWU hu,hl,?_,hm,hp,?_⟩
  · change (suitableQuotientCentralizer h u).relIndex (T : Subgroup G) = 2
    rw [show suitableQuotientCentralizer h u = S from heq]
    exact hindex
  · change Mc ⊓ normalizer (suitableQuotientCentralizer h u : Set G) = _
    rw [show suitableQuotientCentralizer h u = S from heq]
    exact hlocal

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
