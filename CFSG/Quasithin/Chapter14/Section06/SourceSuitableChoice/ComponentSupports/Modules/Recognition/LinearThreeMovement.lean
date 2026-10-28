module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.LinearThreeOrbits
public import Theory.Representation.BinaryOffender.Homogeneous.LinearThreePair

/-!
# Diagram movement of the original terminal seed supports

An inner automorphism preserving a self-normalizing Sylow cannot exchange
its two parabolic overgroups. The actual source parabolic swap is therefore
outer. The intrinsic component quotient marking intertwines this action with
the literal image in H/O₂(H), where the natural-cover inertia theorem forces
movement of the seed. Its support stabilizer has index two in N_T(K).

At the unchanged H=Mc, the exchanged-component source hypotheses supply all
markings. They give two distinct original subgroup supports, their exact
conjugate-span identity and central-overlap separation. Their orbit has a
six-dimensional central quotient and total dimension six, seven, or eight.
No fixed kernel is discarded. This orbit is not yet identified with [U,K].
The cover and FF exclusions, full support exhaustion, normal PSL₂(4)
exclusion and final suitable assembly remain with qt-e-suitable-component-supports.
Original 14.6.18 remains explicit for qt-e-14625-source to discharge.

Source: Aschbacher--Smith 14.6.20--24, printed pp.1037--1039,
and A.1.40--42, printed pp.31--32.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous Representation.OneCohomology
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Subgroup.NormalSylowQuotientAction
variable {G : Type*} [Group G] [Finite G]

private theorem swap_not_inner {B : Type*} [Group B]
    (P J L : Subgroup B) (hP : normalizer (P : Set B) = P)
    (hi : J ⊓ L = P) (hne : J ≠ L) (a : MulAut B)
    (hJ : J.map a.toMonoidHom = L) (hL : L.map a.toMonoidHom = J) :
    ¬ ∃ b, a = MulAut.conj b := by
  rintro ⟨b,rfl⟩
  have hb : b ∈ normalizer (P : Set B) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [←hi,map_inf _ _ _ (MulAut.conj b).injective]
    change J.map (MulAut.conj b).toMonoidHom ⊓ L.map (MulAut.conj b).toMonoidHom = J ⊓ L
    rw [hJ,hL,inf_comm]
  have hbJ : b ∈ J := (show J ⊓ L ≤ J from inf_le_left) (hi.symm ▸ (hP ▸ hb))
  exact hne ((mem_normalizer_iff_map_conj_eq.mp (J.le_normalizer hbJ)).symm.trans hJ)

private def componentImageEquiv
    (H K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    (K ⧸ pCore 2 K) ≃* actorImage H K :=
  (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKH))).symm.trans (cComponentTwoCoreQuotientEquiv hK)

private theorem componentImageEquiv_mk
    (H K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) (k : K) :
    componentImageEquiv H K hKH hK (QuotientGroup.mk' (pCore 2 K) k) =
      (QuotientGroup.mk' (pCore 2 H)).subgroupMap (K.subgroupOf H)
        ((subgroupOfEquivOfLe hKH).symm k) := rfl

private theorem marked_inner_of_image_inner
    (H K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {B : Type*} [Group B] (eK : (K ⧸ pCore 2 K) ≃* B)
    (s : H) (hs : (s:G) ∈ normalizer (K : Set G))
    (hinner : ∃ k : actorImage H K, ∀ x : actorImage H K,
      QuotientGroup.mk' (pCore 2 H) s * x.val * (QuotientGroup.mk' (pCore 2 H) s)⁻¹ =
        k.val * x.val * k.val⁻¹) :
    ∃ b : B, markedCoreAction 2 K eK ⟨s,hs⟩ = MulAut.conj b := by
  let c := componentImageEquiv H K hKH hK
  obtain ⟨k,hk⟩ := hinner
  refine ⟨eK (c.symm k),MulEquiv.ext fun x => ?_⟩
  obtain ⟨x,rfl⟩ := eK.surjective x
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
  rw [markedCoreAction_mk]
  change eK _ = eK (c.symm k) * eK (QuotientGroup.mk' (pCore 2 K) x) * (eK (c.symm k))⁻¹
  rw [←map_inv,←map_mul,←map_mul]
  apply congrArg eK
  apply c.injective
  rw [map_mul,map_mul,map_inv,c.apply_symm_apply]
  apply Subtype.ext
  have he := hk (c (QuotientGroup.mk' (pCore 2 K) x))
  change QuotientGroup.mk' (pCore 2 H) (s * ⟨x,hKH x.property⟩ * s⁻¹) = _
  rw [map_mul,map_mul,map_inv]
  exact he

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

/-- The diagram swap is outer on the actual component image in H/O₂(H). -/
theorem source_l3_component_outer_image
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (b : actorImage H K ≃* Matrix.PSL3Two.SL) :
    ∃ s : ((T : Subgroup G) ⊓ normalizer (K : Set G) : Subgroup G),
      ¬ ∃ k : actorImage H K, ∀ x : actorImage H K,
        let q := QuotientGroup.mk' (pCore 2 H) ⟨s,hH.1.2 s.property.1⟩
        q * x.val * q⁻¹ = k.val * x.val * k.val⁻¹ := by
  let eK := (componentImageEquiv H K hKH hK).trans (b.trans Matrix.PSL3Two.equiv)
  obtain ⟨P,hP,J,L,hJ,hL,hne,hi,hall,s,hsJ,hsL⟩ :=
    source_l3_component_parabolic_swap hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK eK
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let Pq := P.mapSurjective (f := q) (eK.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 K)))
  have hself : normalizer (Pq : Set Matrix.PSL3Two.PSL) = (Pq : Subgroup Matrix.PSL3Two.PSL) :=
    Sylow.self_normalizing_of_surjective Matrix.PSL3Two.equiv.toMonoidHom Matrix.PSL3Two.equiv.surjective
      Matrix.PSL3Two.self_normalizing_sylow Pq
  refine ⟨s,fun hs => ?_⟩
  exact swap_not_inner (Pq : Subgroup Matrix.PSL3Two.PSL) J L hself hi hne _ hsJ hsL
    (marked_inner_of_image_inner H K hKH hK eK ⟨s,hH.1.2 s.property.1⟩ s.property.2 hs)

/-- Every marked homogeneous natural-cover seed is moved by the original
component stabilizer, and its literal support stabilizer has index two. -/
theorem source_l3_seed_stabilizer_index
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H)))}
    (hI : IsIrrPlusWith a.representation (actorImage H K)
      (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I)
    (b : ChapterB.QuasisimpleSource.ActionEquiv
      (centralQuotientRepresentation a.representation (actorImage H K) I hI.isIrrPlus.choose)
      (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3)) :
    let W := (originalSection a).subspacePreimage I
    let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
    (∃ s : S, (s:G) ∉ normalizer (W : Set G)) ∧
      (normalizer (W : Set G)).relIndex S = 2 := by
  let W := (originalSection a).subspacePreimage I
  let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
  let R := actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))
  let q := QuotientGroup.mk' (pCore 2 H)
  have hSH : S ≤ H := inf_le_left.trans hH.1.2
  obtain ⟨s,hs⟩ := source_l3_component_outer_image
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK b.groupEquiv
  have hn : (s:G) ∉ normalizer (W : Set G) := by
    intro hh
    exact hs ((source_seed_normalizer_iff_inner T H hH K hKH hK a hI b s).mp hh)
  refine ⟨⟨s,hn⟩,?_⟩
  have hR : actorImage H S = R := source_component_normalizer_image T H hH K hKH hK
  have hmove : orbitSpan a.representation R I ≠ I := by
    intro he
    have hinv : R ≤ subspaceStabilizer a.representation I :=
      he ▸ orbitSpan_invariant a.representation R I
    let sh : H := ⟨s,hSH s.property⟩
    have hqs : q sh ∈ R := hR ▸ (show q sh ∈ actorImage H S from ⟨sh,s.property,rfl⟩)
    apply hn
    exact ((originalSection a).mem_normalizer_subspacePreimage_iff I sh).mpr
      ((subspace_map_eq_iff a.representation I (q sh)).mpr (hinv hqs))
  have hindex := hI.linear_three_stabilizer_index a.representation b.groupEquiv hmove
  have hN : (normalizer (W : Set G)).subgroupOf H =
      (subspaceStabilizer a.representation I).comap q := by
    ext h
    change (h:G) ∈ normalizer (W : Set G) ↔ q h ∈ subspaceStabilizer a.representation I
    rw [(originalSection a).mem_normalizer_subspacePreimage_iff I h]
    exact subspace_map_eq_iff a.representation I (q h)
  rw [←relIndex_subgroupOf (H := normalizer (W : Set G)) hSH,hN,relIndex_comap]
  change (subspaceStabilizer a.representation I).relIndex (actorImage H S) = 2
  rw [hR]
  exact hindex

/-- At H=Mc the original exchanged-component hypotheses give two distinct
literal seed supports, index two in N_T(K), and a six-dimensional central
quotient of their orbit. The total dimension is six, seven, or eight. -/
theorem terminal_nonnormal_moved_seed_pair
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T),
      ∃ (I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
        (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))))
        (hI : IsIrrPlusWith a.representation (actorImage Mc K)
          (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I),
      Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
        (centralQuotientRepresentation a.representation (actorImage Mc K) I hI.isIrrPlus.choose)
        (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3)) ∧
      (Module.finrank (ZMod 2) I = 3 ∨ Module.finrank (ZMod 2) I = 4) ∧
      let c := originalSection a
      let W := c.subspacePreimage I
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      ∃ t : S, (t:G) ∉ normalizer (W : Set G) ∧
        conjugateSpanBy W S = W ⊔ W.map (MulAut.conj (t:G)⁻¹).toMonoidHom ∧
        W ⊓ W.map (MulAut.conj (t:G)⁻¹).toMonoidHom ≤ centralizer (K : Set G) ∧
        K ≤ normalizer (W.map (MulAut.conj (t:G)⁻¹).toMonoidHom : Set G) ∧
        (normalizer (W : Set G)).relIndex S = 2 ∧
        Module.finrank (ZMod 2) ((c.imageSpace (conjugateSpanBy W S)).map
          (fixedSpace a.representation (actorImage Mc K)).mkQ) = 6 ∧
        (Module.finrank (ZMod 2) (c.imageSpace (conjugateSpanBy W S)) = 6 ∨
          Module.finrank (ZMod 2) (c.imageSpace (conjugateSpanBy W S)) = 7 ∨
          Module.finrank (ZMod 2) (c.imageSpace (conjugateSpanBy W S)) = 8) := by
  obtain ⟨hU,a,I,hI,hmark,hker,hdim,halt,_⟩ := terminal_nonnormal_central_natural_support
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  let := hU
  let b := Classical.choice hmark
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  let c := originalSection a
  let W := c.subspacePreimage I
  let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
  let R := actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))
  obtain ⟨⟨s,hs⟩,hindex⟩ := source_l3_seed_stabilizer_index
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK a hI b
  obtain ⟨t,ht,hspan,_⟩ := source_seed_two_conjugates T Mc hout K hKM hK a hI
    b.groupEquiv (by omega)
  have hnt : (t:G) ∉ normalizer (W : Set G) := by
    intro hn
    have he : W.map (MulAut.conj (t:G)⁻¹).toMonoidHom = W :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (W : Set G)).inv_mem hn)
    have hh : W.map (MulAut.conj (s:G)⁻¹).toMonoidHom = W :=
      (ht s).elim id (fun h => h.trans he)
    exact hs ((normalizer (W : Set G)).inv_mem_iff.mp (mem_normalizer_iff_map_conj_eq.mpr hh))
  have hsep := (source_component_seed_geometry hG T hempty hM hunique hmany hcard e hab hsolv
    Mc hout K hKM hK a hI.isIrrPlus).2.2.2.2 t.val t.property.1 t.property.2 hnt
  have hR : actorImage Mc S = R := source_component_normalizer_image T Mc hout K hKM hK
  have horbit : c.imageSpace (conjugateSpanBy W S) = orbitSpan a.representation R I := by
    rw [originalSection_support_orbit a S (inf_le_left.trans hout.1.2) I,hR]
  have hmove : orbitSpan a.representation R I ≠ I := by
    intro he
    have hinv : R ≤ subspaceStabilizer a.representation I :=
      he ▸ orbitSpan_invariant a.representation R I
    let sh : Mc := ⟨s,hout.1.2 s.property.1⟩
    have hqs : QuotientGroup.mk' (pCore 2 Mc) sh ∈ R :=
      hR ▸ (show QuotientGroup.mk' (pCore 2 Mc) sh ∈ actorImage Mc S from ⟨sh,s.property,rfl⟩)
    apply hs
    exact (c.mem_normalizer_subspacePreimage_iff I sh).mpr
      ((subspace_map_eq_iff a.representation I _).mpr (hinv hqs))
  obtain ⟨_,_,_,_,hd,hall⟩ := hI.linear_three_moved_pair a.representation
    b.groupEquiv b.linearEquiv b.intertwines hmove
  refine ⟨hU,a,I,hI,hmark,halt,t,hnt,hspan,hsep.1,hsep.2,hindex,?_,?_⟩
  · rw [horbit]; exact hd
  · rw [horbit]; exact hall

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
