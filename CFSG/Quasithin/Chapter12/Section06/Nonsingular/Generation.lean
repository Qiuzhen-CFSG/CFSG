module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.MovedModule
public import Theory.Representation.BinaryPermutation.EightNonsingularStabilizer.Generation

/-!
# Generation by the weight-two point residuals in V_v

The genuine five-dimensional core marking identifies each pair word with
an actual vector u in V_v. Its original quotient projection identifies the
image of L_u=O²(C_L(u)) with the corresponding A₆ point fixer. These images
generate A₈. The original O₂(L) centralizes V and therefore normalizes every
L_u. Consequently their span is normal in L with two-group quotient;
perfectness of L proves that the span equals L.

The source application constructs the marking and proves L(v)=L for every
nonsingular v, retaining conjugation, V, C_V(L), and the original quotient
map. The following centralizer application discharges the generation input
of 12.6.11. Its permutation input remains explicit and must be proved by
the component argument. Component recognition, the block and splitting
arguments, and the fixed-space elimination still remain with the source
assembly; this module does not establish 12.6.2 or 12.6.23.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
Lemma 12.6.10 and the following proof of 12.6.11, printed p.825.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open BinaryPermutation BinaryPermutation.EightNonsingular
open scoped IsMulCommutative

private theorem perfect_eq_top_of_image (X Y : Type*) [Group X] [Finite X] [Group Y]
    [Group.IsPerfect X] (f : X →* Y) (B : Subgroup X)
    (hk : IsPGroup 2 f.ker) (hmap : B.map f = ⊤)
    (hn : f.ker ≤ normalizer (B : Set X)) : B = ⊤ := by
  have hs : B ⊔ f.ker = ⊤ := by
    have hh := congrArg (comap f) hmap
    simpa only [comap_map_eq,comap_top] using hh
  let : B.Normal := normalizer_eq_top_iff.mp (by
    apply top_unique
    rw [←hs]
    exact sup_le B.le_normalizer hn)
  have hp := isPGroup_quotient_of_sup_eq_top B f.ker hk hs
  by_contra hB
  let : Nontrivial (X ⧸ B) := QuotientGroup.nontrivial_iff.mpr hB
  let : Group.IsNilpotent (X ⧸ B) := hp.isNilpotent
  exact Group.IsPerfect.not_isSolvable (X ⧸ B) inferInstance

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private noncomputable def pairResidualSpan (L W : Subgroup G) [IsElementaryAbelian 2 W]
    (E : core (Fin 6) ≃ₗ[ZMod 2] Additive W) : Subgroup G :=
  ⨆ a : Fin 6, ⨆ b : Fin 6, ⨆ (_ : a ≠ b), Lv L ((E (sixPair a b)).toMul : G)

private theorem SourceHypothesis.pairResidualSpan_eq
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hWV : W ≤ V)
    (E : core (Fin 6) ≃ₗ[ZMod 2] Additive W)
    (i j : Fin 8) (hij : i ≠ j)
    (hproj : ∀ w, D.coordinates (Submodule.Quotient.mk (Additive.ofMul
      (show V from ⟨(E w).toMul, hWV (E w).toMul.property⟩))) =
        coreToNatural (Fin 8) (extendSix i j hij w)) :
    pairResidualSpan L W E = L := by
  let B := pairResidualSpan L W E
  have hBL : B ≤ L := iSup_le fun a => iSup_le fun b => iSup_le fun hab => Lv_le_L _ _
  have himage : (B.subgroupOf L).map D.actorMap = ⊤ := by
    apply complementary_pairFixers_generate i j
    intro a b hai haj hbi hbj hab
    obtain ⟨a',rfl⟩ := complementLetters_exhaust i j hij a hai haj
    obtain ⟨b',rfl⟩ := complementLetters_exhaust i j hij b hbi hbj
    have hab' : a' ≠ b' := fun he => hab (congrArg (complementLetters i j hij) he)
    let u : V := ⟨(E (sixPair a' b')).toMul, hWV (E (sixPair a' b')).toMul.property⟩
    have hp : coreToNatural (Fin 8)
        (pair (complementLetters i j hij a') (complementLetters i j hij b')) =
          D.coordinates (Submodule.Quotient.mk (Additive.ofMul u)) := by
      rw [←extendSix_pair]
      exact (hproj _).symm
    rw [←D.Lv_image_pair u _ _ hab hp]
    apply map_mono
    apply subgroupOf_mono
    exact le_iSup_of_le a' (le_iSup_of_le b' (le_iSup_of_le hab' le_rfl))
  have hcore : L.pCoreIn 2 ≤ centralizer (V : Set G) := by
    rw [←H.centralizer_eq_core]
    exact inf_le_right
  have hnorm : L.pCoreIn 2 ≤ normalizer (B : Set G) := by
    apply le_trans _ (iInf_normalizer_le_normalizer_iSup _)
    apply le_iInf
    intro a
    apply le_trans _ (iInf_normalizer_le_normalizer_iSup _)
    apply le_iInf
    intro b
    apply le_trans _ (iInf_normalizer_le_normalizer_iSup _)
    apply le_iInf
    intro hab
    apply le_trans _ (Mv_le_normalizer_Lv L _)
    apply le_inf ((pCoreIn_le 2 L).trans L.le_normalizer)
    exact hcore.trans (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr (hWV (E (sixPair a b)).toMul.property)))
  have hcomp := H.source.maximal_faithful.1.1.1
  let : Group.IsPerfect (L.subgroupOf (LT T L)) := hcomp.perfect
  let e := subgroupOfEquivOfLe (show L ≤ LT T L from le_sup_left)
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hh : B.subgroupOf L = ⊤ := by
    refine perfect_eq_top_of_image L _ D.actorMap _ ?_ himage ?_
    · rw [D.actorMap_ker H.chosen H.source.quasisimple]
      exact pCore_isPGroup
    · rw [D.actorMap_ker H.chosen H.source.quasisimple]
      intro r hr x
      exact hnorm (mem_map_of_mem L.subtype hr) (x : G)
  have hm := congrArg (map L.subtype) hh
  simpa only [map_subgroupOf_eq_of_le hBL, ←MonoidHom.range_eq_map, range_subtype] using hm


/-- The actual weight-two vectors in the marked subgroup W, embedded in G. -/
noncomputable def weightTwoPoints (W : Subgroup G) [IsElementaryAbelian 2 W]
    (E : core (Fin 6) ≃ₗ[ZMod 2] Additive W) : Set G :=
  {u | ∃ w : core (Fin 6), hammingNorm w.val = 2 ∧ ((E w).toMul : G) = u}

/-- The source L(v), generated by O²(C_L(u)) for the marked weight-two vectors. -/
noncomputable def weightTwoResiduals (L W : Subgroup G) [IsElementaryAbelian 2 W]
    (E : core (Fin 6) ≃ₗ[ZMod 2] Additive W) : Subgroup G :=
  ⨆ u ∈ weightTwoPoints W E, Lv L u

/-- Lift the complementary-pair calculation through the original action kernel.
Only the compatibility of this core marking with V/C_V(L) is used. -/
theorem SourceHypothesis.weightTwoResiduals_eq
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hWV : W ≤ V)
    (E : core (Fin 6) ≃ₗ[ZMod 2] Additive W)
    (i j : Fin 8) (hij : i ≠ j)
    (hproj : ∀ w, D.coordinates (Submodule.Quotient.mk (Additive.ofMul
      (show V from ⟨(E w).toMul, hWV (E w).toMul.property⟩))) =
        coreToNatural (Fin 8) (extendSix i j hij w)) :
    weightTwoResiduals L W E = L := by
  apply le_antisymm (iSup_le fun u => iSup_le fun _ => Lv_le_L L u)
  nth_rw 1 [←H.pairResidualSpan_eq D W hWV E i j hij hproj]
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  apply iSup_le
  intro hab
  exact le_iSup_of_le ((E (sixPair a b)).toMul : G)
    (le_iSup_of_le ⟨sixPair a b,sixPair_weight a b hab,rfl⟩ le_rfl)

/-- Lemma 12.6.10 on the original V_v: construct an equivariant core marking
over the original quotient projection, and prove that its weight-two point
residuals generate L itself. No local generation premise is assumed. -/
theorem SourceHypothesis.nonsingular_weightTwo_generation
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    let := Vv_elementary H.chosen.normalizes (v : G)
    ∃ (i j : Fin 8) (hij : i ≠ j)
      (hp : coreToNatural (Fin 8) (pair i j) =
        D.coordinates (Submodule.Quotient.mk (Additive.ofMul v)))
      (E : core (Fin 6) ≃ₗ[ZMod 2] Additive (Vv L V (v : G))),
      (∀ l : Lv L (v : G), ∀ w,
        E (alternatingCoreRepresentation (Fin 6) (D.localSixMap v i j hij hp l) w) =
          seedRepresentation (Lv L (v : G)) (Vv L V (v : G))
            (Lv_normalizes_Vv L V (v : G)) l (E w)) ∧
      (∀ w, D.coordinates (Submodule.Quotient.mk (Additive.ofMul
        (show V from ⟨(E w).toMul, Vv_le_V H.chosen.normalizes _ (E w).toMul.property⟩))) =
          coreToNatural (Fin 8) (extendSix i j hij w)) ∧
      weightTwoResiduals L (Vv L V (v : G)) E = L := by
  let := Vv_elementary H.chosen.normalizes (v : G)
  obtain ⟨i,j,hij,hp⟩ := nonsingular_pair _ hv
  obtain ⟨E,hE,hproj⟩ := D.local_core_marking H.chosen v i j hij hp
  exact ⟨i,j,hij,hp,E,hE,hproj,
    H.weightTwoResiduals_eq D _ (Vv_le_V H.chosen.normalizes _) E i j hij hproj⟩

/-- Permuting the actual generating point residuals forces normalization of L. -/
theorem mem_M_of_permutes_weightTwoResiduals
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (E : core (Fin 6) ≃ₗ[ZMod 2] Additive W)
    (hgen : weightTwoResiduals L W E = L) (g : G)
    (hg : ∀ u ∈ weightTwoPoints W E, ∃ w ∈ weightTwoPoints W E,
      (Lv L u).map (MulAut.conj g).toMonoidHom = Lv L w) : g ∈ M L := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · conv_lhs => rw [←hgen,weightTwoResiduals,Subgroup.map_iSup]
    apply iSup_le
    intro u
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hu
    obtain ⟨w,hw,he⟩ := hg u hu
    exact he.le.trans (Lv_le_L L w)
  · rw [card_map_of_injective (MulAut.conj g).injective]

/-- The literal centralizer application in 12.6.11, with generation discharged.
The component argument must still prove permutation of these residuals; this
conditional application does not assert 12.6.11 or Theorem 12.6.2. -/
theorem SourceHypothesis.local_centralizer_control_of_permutation
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) :
    let := Vv_elementary H.chosen.normalizes (v : G)
    ∀ (E : core (Fin 6) ≃ₗ[ZMod 2] Additive (Vv L V (v : G)))
      (i j : Fin 8) (hij : i ≠ j),
      (∀ w, D.coordinates (Submodule.Quotient.mk (Additive.ofMul
        (show V from ⟨(E w).toMul, Vv_le_V H.chosen.normalizes _ (E w).toMul.property⟩))) =
          coreToNatural (Fin 8) (extendSix i j hij w)) →
      (∀ g ∈ Gv (v : G) ⊓ centralizer (Vv L V (v : G) : Set G),
        ∀ u ∈ weightTwoPoints (Vv L V (v : G)) E,
          ∃ w ∈ weightTwoPoints (Vv L V (v : G)) E,
            (Lv L u).map (MulAut.conj g).toMonoidHom = Lv L w) →
      Gv (v : G) ⊓ centralizer (Vv L V (v : G) : Set G) ≤ M L := by
  let := Vv_elementary H.chosen.normalizes (v : G)
  dsimp only
  intro E i j hij hproj hperm g hg
  have hgen := H.weightTwoResiduals_eq D _ (Vv_le_V H.chosen.normalizes _) E i j hij hproj
  exact mem_M_of_permutes_weightTwoResiduals _ E hgen g (hperm g hg)

end CFSG.Quasithin.Chapter12.Section06
