module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Geometry
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Calculus
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.PointFusion
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.GenerationOne

/-!
# First-closure generators in the original exterior actor

Lift subgroups of the literal actor image with unchanged relative index and
apply E.3.7 with binary corank additivity. This proves the fixed-space-family
clause of E.3.10 on the chosen exterior action. The two restricted three-space
images have rank at most two, so r(G,V)>3 gives reverse normalization.
Controlled point fusion and the elementary point span then exclude both
commutator lines. Every corank-one generator therefore lies in the model
radical and fixes V₆. Taking the actual weak-closure span gives the C₁ bound
and its original H-star generation consumer.

Source: Aschbacher--Smith, 12.5.10 and 12.5.11(1), printed p.821,
using E.3.7--10 and E.3.32. The earlier numerical, point-fusion and local
normalizer inputs remain explicit; no exclusion callback is assumed.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The fixed-space clause of E.3.10 in the literal exterior actor. -/
theorem actorImage_smallIndex_of_corank (g : G) {A : Subgroup G}
    (hAW : A ≤ V.map (MulAut.conj g).toMonoidHom)
    (hAH : A ≤ L ⊔ (T : Subgroup G)) (b k : ℕ)
    (hb : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A ≤ b)
    (hs : let := D.elementary; (b + k : ℕ) ≤ (globalS V).toNat) :
    SL5ExteriorSquare.HasSmallIndexFixedSpaceProperty k (s.actorImage A) := by
  let := D.elementary
  let W := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  intro B hB hsmall
  obtain ⟨C, hCA, hCB, hcor⟩ := s.lift_actorImage hAH B hB
  have hc : (subgroupCorank W C : ℕ∞) < globalS V := by
    rw [← ENat.natCast_toNat (globalS_ne_top V)]
    apply ENat.natCast_lt_natCast.mpr
    rw [offender_corank_add hCA hAW, hcor]
    omega
  have ha : (subgroupCorank W A : ℕ∞) < globalS V := by
    apply lt_of_le_of_lt _ hc
    exact_mod_cast (show subgroupCorank W A ≤ subgroupCorank W C by
      change subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A ≤ _
      rw [offender_corank_add hCA hAW]
      exact Nat.le_add_right _ _)
  apply s.marking.subspace_injective
  rw [← hCB, s.subspace_fixedSpace hAH, s.subspace_fixedSpace (hCA.trans hAH)]
  exact (lemma_E_3_7 g (le_inf hAW (hAH.trans s.normalizes)) ha).trans
    (lemma_E_3_7 g (le_inf (hCA.trans hAW) ((hCA.trans hAH).trans s.normalizes)) hc).symm

/-- E.3.10's actual nontrivial elementary fixed-space family in the chosen
exterior image; no unrelated representation or family tag is substituted. -/
theorem actorImage_mem_fixedSpaceFamily (g : G) {A : Subgroup G}
    (hAW : A ≤ V.map (MulAut.conj g).toMonoidHom)
    (hAH : A ≤ L ⊔ (T : Subgroup G)) (b k : ℕ) (hk : 0 < k)
    (hb : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A ≤ b)
    (hs : let := D.elementary; (b + k : ℕ) ≤ (globalS V).toNat)
    (hcomm : ⁅V, A⁆ ≠ ⊥) :
    s.actorImage A ∈ fixedSpaceFamily
      (SL5TenDimensional.exteriorAction 2) k := by
  let := D.elementary
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 A := offender_elementary_of_le hAW
  let _ := IsElementaryAbelian.subgroupOf (p := 2) hAH
  let _ : IsElementaryAbelian 2 (s.actorImage A) := IsElementaryAbelian.map _
  refine ⟨hk, ⟨?_, inferInstance⟩, s.actorImage_smallIndex_of_corank g hAW hAH b k hb hs⟩
  intro he
  have hf := s.subspace_fixedSpace hAH
  rw [he, BinaryOffender.fixedSpace_bot, s.marking.subspace_top] at hf
  exact hcomm (commutator_eq_bot_iff_le_centralizer.mpr (inf_eq_left.mp hf.symm))

omit [Finite G] in
/-- Exact transport of the commutator of an arbitrary exterior subspace. -/
theorem subspace_commutator_of_subspace {A : Subgroup G}
    (hA : A ≤ L ⊔ (T : Subgroup G))
    (W : Submodule (ZMod 2) SL5ExteriorSquare.V) :
    s.marking.subspace (BinaryOffender.subspaceCommutator
      (SL5TenDimensional.exteriorAction 2) W (s.actorImage A)) =
        ⁅s.marking.subspace W, A⁆ := by
  let : Module (ZMod 2) (Additive (Multiplicative SL5ExteriorSquare.V)) :=
    inferInstanceAs (Module (ZMod 2) SL5ExteriorSquare.V)
  let ρ : Representation (ZMod 2) SL5TenDimensional.Group
      (Additive (Multiplicative SL5ExteriorSquare.V)) := SL5TenDimensional.exteriorAction 2
  let f : A →* SL5TenDimensional.Group := s.actor.comp (inclusion hA)
  have hf : f.range = s.actorImage A := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨inclusion hA a, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hp : BinaryOffender.binarySubgroup W =
      ((s.marking.subspace W).subgroupOf V).map s.marking.coordinates.toMonoidHom := by
    change _ = ((((BinaryOffender.binarySubgroup W).comap
      s.marking.coordinates.toMonoidHom).map V.subtype).comap V.subtype).map
        s.marking.coordinates.toMonoidHom
    rw [comap_map_eq_self_of_injective V.subtype_injective,
      map_comap_eq_self_of_surjective s.marking.coordinates.surjective]
  have he := BinaryOffender.commutator_image_eq ρ V (s.marking.subspace W) A
    (hA.trans s.normalizes) (s.marking.subspace_le _) f s.marking.coordinates.toMonoidHom
    (fun a v => (congrArg Multiplicative.toAdd (s.equivariant (inclusion hA a) v)).symm)
    W hp
  rw [hf] at he
  have hc : ⁅s.marking.subspace W, A⁆ ≤ V :=
    (commutator_mono (s.marking.subspace_le _) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hA.trans s.normalizes))
  change ((BinaryOffender.binarySubgroup
    (BinaryOffender.subspaceCommutator ρ W (s.actorImage A))).comap
      s.marking.coordinates.toMonoidHom).map V.subtype = _
  rw [← he, comap_map_eq_self_of_injective s.marking.coordinates.injective,
    map_subgroupOf_eq_of_le hc]

/-- Lift the pointwise kernel on a small exterior subspace. The rank bound
on its actual restricted image gives reverse normalization by E.3.32. -/
theorem subspace_normalizes_conjugate (g : G) {A : Subgroup G}
    (hAW : A ≤ V.map (MulAut.conj g).toMonoidHom)
    (hAT : A ≤ (T : Subgroup G))
    (hb : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A ≤ 1)
    (hr : (3 : ℕ∞) < globalR V)
    (W : Submodule (ZMod 2) SL5ExteriorSquare.V)
    (hstable : s.actorImage A ≤ BinaryOffender.subspaceStabilizer
      (SL5TenDimensional.exteriorAction 2) W)
    (hrank : BinaryOffender.rank (BinaryOffender.restrictedSubgroup
      (SL5TenDimensional.exteriorAction 2) W (s.actorImage A)) ≤ 2) :
    s.marking.subspace W ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  let := D.elementary
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  let B := BinaryOffender.subspaceKernel (SL5TenDimensional.exteriorAction 2) W
    (s.actorImage A)
  obtain ⟨C, hCA, he, hc⟩ := s.lift_actorImage (hAT.trans le_sup_right) B
    (BinaryOffender.subspaceKernel_le _ _ _)
  have hcor : subgroupCorank A C ≤ 2 := by
    rw [hc, SL5ExteriorSquare.FlagThreeActions.kernel_relIndex_eq_card_image
      _ _ _ hstable]
    exact hrank
  have hfix : s.marking.subspace W ≤ centralizer (C : Set G) := by
    apply le_trans (b := V ⊓ centralizer (C : Set G)) _ inf_le_right
    rw [← s.subspace_fixedSpace (hCA.trans (hAT.trans le_sup_right)), he]
    exact s.marking.subspace_mono (BinaryOffender.le_fixedSpace_subspaceKernel _ _ _)
  apply hfix.trans
  apply centralizer_le_normalizer_of_corank_lt_globalR (hCA.trans hAW)
  rw [globalR_map_equiv, offender_corank_add hCA hAW]
  exact lt_of_le_of_lt (by exact_mod_cast (show
    subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A + subgroupCorank A C ≤ 3 by
      omega)) hr

end SylowExteriorMarking

/-- Controlled point fusion and the elementary point span exclude both source
commutator lines, once the small subspace has been shown to normalize Vᵍ. -/
theorem first_commutator_line_exclusion (s : SylowExteriorMarking D)
    (p : PointControl s.marking) [IsElementaryAbelian 2 s.marking.U]
    (g : G) {A : Subgroup G} (hAW : A ≤ V.map (MulAut.conj g).toMonoidHom)
    (hAT : A ≤ (T : Subgroup G))
    (hb : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A ≤ 1)
    (hr : (3 : ℕ∞) < globalR V)
    (W : Submodule (ZMod 2) SL5ExteriorSquare.V)
    (hstable : s.actorImage A ≤ BinaryOffender.subspaceStabilizer
      (SL5TenDimensional.exteriorAction 2) W)
    (hrank : BinaryOffender.rank (BinaryOffender.restrictedSubgroup
      (SL5TenDimensional.exteriorAction 2) W (s.actorImage A)) ≤ 2) :
    ¬ SL5ExteriorSquare.V₁ ≤ BinaryOffender.subspaceCommutator
      (SL5TenDimensional.exteriorAction 2) W (s.actorImage A) := by
  let : IsElementaryAbelian 2 (conjugateSpanBy V (s.marking.Gi 1)) :=
    ‹IsElementaryAbelian 2 s.marking.U›
  intro hline
  have hn := s.subspace_normalizes_conjugate g hAW hAT hb hr W hstable hrank
  have hc : ⁅s.marking.subspace W, A⁆ ≤ V.map (MulAut.conj g).toMonoidHom :=
    (commutator_mono le_rfl hAW).trans
      (le_normalizer_iff_commutator_le_right.mp hn)
  have hl : s.marking.Vi 1 ≤ ⁅s.marking.subspace W, A⁆ := by
    rw [← s.subspace_commutator_of_subspace (hAT.trans le_sup_right)]
    exact s.marking.subspace_mono hline
  obtain ⟨c, he⟩ := exists_centralizer_conjugator_of_element_fusion
    (fun x hx => by
      obtain ⟨l, hl, he⟩ := p.fusion x hx
      exact ⟨l, D.normalizes hl, he.symm⟩) (hc (hl p.point_mem))
  have hcG : (c : G) ∈ s.marking.Gi 1 := p.point_centralizer.symm ▸ c.property
  have hWU : V.map (MulAut.conj g).toMonoidHom ≤ s.marking.U := by
    rw [← he]
    rintro x ⟨v, hv, rfl⟩
    exact subset_closure ⟨c, hcG, v, hv, rfl⟩
  have hbot : ⁅s.marking.subspace W, A⁆ ≤ ⊥ := by
    apply (commutator_mono
      ((s.marking.subspace_le W).trans (le_conjugateSpanBy V (s.marking.Gi 1)))
      (hAW.trans hWU)).trans
    exact le_of_eq (commutator_self_eq_bot_iff.mpr inferInstance)
  exact s.marking.z_ne_one (mem_bot.mp (hbot (hl s.marking.z_mem_V₁)))

/-- Every original corank-one generator has radical-six image and fixes V₆.
Both line exclusions are discharged using the actual controlled point fusion. -/
theorem first_generator_geometry (s : SylowExteriorMarking D)
    (p : PointControl s.marking) [IsElementaryAbelian 2 s.marking.U]
    (g : G) {A : Subgroup G} (hAW : A ≤ V.map (MulAut.conj g).toMonoidHom)
    (hAT : A ≤ (T : Subgroup G))
    (hb : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A ≤ 1)
    (hr : (3 : ℕ∞) < globalR V)
    (hs : let := D.elementary; globalS V = 3) :
    s.actorImage A ≤ SL5ExteriorSquare.parabolicResidualTwoCore 4 ∧
      A ≤ centralizer (s.marking.Vi 6 : Set G) := by
  let := D.elementary
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 A := offender_elementary_of_le hAW
  let _ := IsElementaryAbelian.subgroupOf (p := 2) (hAT.trans le_sup_right :
    A ≤ L ⊔ (T : Subgroup G))
  let _ : IsElementaryAbelian 2 (s.actorImage A) := IsElementaryAbelian.map _
  have hf := s.actorImage_le_flag hAT
  have hsmall := s.actorImage_smallIndex_of_corank g hAW (hAT.trans le_sup_right)
    1 2 hb (by change 1 + 2 ≤ (globalS V).toNat; rw [hs]; decide)
  obtain ⟨hle, hfix⟩ := ExteriorGeometry.smallIndex_two_module_containment (s.actorImage A)
    hf hsmall
    (first_commutator_line_exclusion s p g hAW hAT hb hr _
      (hf.trans SL5ExteriorSquare.flagGroup_stabilizes_V₃)
      (SL5ExteriorSquare.rank_restricted_V₃_le_two hf))
    (first_commutator_line_exclusion s p g hAW hAT hb hr _
      (hf.trans SL5ExteriorSquare.flagGroup_stabilizes_V₃')
      (SL5ExteriorSquare.rank_restricted_V₃'_le_two hf))
  refine ⟨hle, le_centralizer_iff.mpr ?_⟩
  have hh := s.marking.subspace_mono hfix
  rw [s.subspace_fixedSpace (hAT.trans le_sup_right)] at hh
  exact hh.trans inf_le_right

/-- The first weak closure fixes the literal V₆, as required by 12.5.10(2). -/
theorem first_centralizes_V₆ (s : SylowExteriorMarking D)
    (p : PointControl s.marking) [IsElementaryAbelian 2 s.marking.U]
    (hr : (3 : ℕ∞) < globalR V)
    (hs : let := D.elementary; globalS V = 3) :
    indexedWeakClosure V (T : Subgroup G) 1 ≤
      centralizer (s.marking.Vi 6 : Set G) := by
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  rintro A ⟨⟨g, hAW, hindex⟩, hAT⟩
  apply (first_generator_geometry s p g hAW hAT ?_ hr hs).2
  simp only [subgroupCorank, hindex]
  decide

/-- The whole first weak closure has image inside the literal model radical. -/
theorem first_actorImage_le_radical (s : SylowExteriorMarking D)
    (p : PointControl s.marking) [IsElementaryAbelian 2 s.marking.U]
    (hr : (3 : ℕ∞) < globalR V)
    (hs : let := D.elementary; globalS V = 3) :
    s.actorImage (indexedWeakClosure V (T : Subgroup G) 1) ≤
      SL5ExteriorSquare.parabolicResidualTwoCore 4 := by
  let H := L ⊔ (T : Subgroup G)
  let P := ((SL5ExteriorSquare.parabolicResidualTwoCore 4).comap s.actor).map H.subtype
  have hP : indexedWeakClosure V (T : Subgroup G) 1 ≤ P := by
    rw [weakClosure_eq_sSup_gamma]
    apply sSup_le
    rintro A ⟨⟨g, hAW, hindex⟩, hAT⟩
    have hle := (first_generator_geometry s p g hAW hAT
      (by simp only [subgroupCorank, hindex]; decide) hr hs).1
    intro a ha
    let aH : H := ⟨a, (le_sup_right : (T : Subgroup G) ≤ H) (hAT ha)⟩
    exact ⟨aH, hle ⟨aH, ha, rfl⟩, rfl⟩
  rintro x ⟨a, ha, rfl⟩
  obtain ⟨b, hb, he⟩ := hP ha
  have hba : b = a := Subtype.ext he
  exact hba ▸ hb

/-- The actual C₁-centralizer is contained in M. -/
theorem first_centralizer_le (s : SylowExteriorMarking D)
    (p : PointControl s.marking) [IsElementaryAbelian 2 s.marking.U]
    (hr : (3 : ℕ∞) < globalR V)
    (hs : let := D.elementary; globalS V = 3)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M) :
    centralizer (weakCentralizer V (T : Subgroup G) 1 : Set G) ≤ s.marking.M :=
  centralizer_weakCentralizer_one_le s.marking hG₆ (first_centralizes_V₆ s p hr hs)

/-- Literal application to the original H-star generation consumer. -/
theorem generation_ne_one_of_first_geometry (s : SylowExteriorMarking D)
    (p : PointControl s.marking) [IsElementaryAbelian 2 s.marking.U]
    (hr : (3 : ℕ∞) < globalR V)
    (hs : let := D.elementary; globalS V = 3)
    (hN : normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ s.marking.M)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    generationParameter H ≠ 1 :=
  generation_ne_one_of_V₆_fixed s.marking hs hN hG₆
    (first_centralizes_V₆ s p hr hs) hH

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
