module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.CartanJoinSp4
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import CFSG.Quasithin.ChapterA.Section04.Modules
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstPrimeLinear

/-!
# Fixed-layer vanishing and faithfulness of the symplectic triangle join

A strict first-component enlargement forces C_V(L) = 1. If that fixed
layer were nontrivial, its normalizer would contain LT and the containing
component K. Nonsolvable uniqueness puts this normalizer inside N_G(L),
and the actual first-component comparison would then give K = L₁.

In the symplectic marking, V meets the Sylow center nontrivially. A central
seed vector lies in the first flag line and is fixed by L₁. Since L₁ and
L₂ generate L and C_V(L) is trivial, L₂ moves the Sylow omega-center.
For a T-normalized local component I containing L₂, characteristic two
puts that center in the omega-center of O₂(IT). Its nonzero commutator
lies in the intrinsic signalizer module of I. Thus I belongs to the
actual faithful local family.

The final application uses I = K₀ ∨ L₂ from the common-normal construction
and supplies its faithful-family membership along with relative normality,
He membership, Cartan containment and both three-rank identities. It does
not assume a natural module for I or a recognized quotient for I.
The nontrivial common normal subgroup, recognition, maximal-local membership,
SL₃(4) exclusion and both orientations remain with
qt-d-1222-natural-relative-components. Earlier flag/Cartan inputs retain
their original producers and final discharge by
qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.762--764; 1.2.7 and A.4.8(4).
-/

open Subgroup Theory.GroupTheory Stellmacher
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
open ChapterA.Section04 Chapter1.Section02.Adequate
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

private theorem local_faithful_of_sylow_center_movement
    (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T) {I : Subgroup G}
    (hI : I ∈ Chapter1.L G T)
    (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    (hm : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ centralizer (I : Set G)) :
    I ∈ MainForward.faithfulLocalComponents T := by
  let J := I ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  have hJ : J ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_6 T hE ⟨hI.2.2,fun _ hx => (show (T : Subgroup G) ≤ J from le_sup_right) hx⟩
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ] using
      pCoreIn_le_sylow J (T.subtype hTJ)
  have hJI : J ≤ normalizer (I : Set G) := sup_le I.le_normalizer hTI
  have hJQ : J ≤ normalizer (Q : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hIQ : I.pCoreIn 2 ≤ Q := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I)
    ((pCoreIn_le 2 I).trans le_sup_left)
    (hJI.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I)))
  have hcomm : ⁅I,Q⁆ ≤ I.pCoreIn 2 := by
    apply le_trans _ (inf_pCoreIn_le_of_le 2 (show I ≤ J from le_sup_left))
    exact le_inf (le_normalizer_iff_commutator_le_left.mp (hQT.trans hTI))
      (le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hJQ))
  have hZ : omegaOneCenterAmbient (T : Subgroup G) ≤ omegaOneCenterAmbient Q := by
    intro z hz
    obtain ⟨hzT,hz2,hzc⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    exact ⟨hJ ⟨hTJ hzT,fun q hq => hzc q (hQT hq)⟩,hz2,
      fun q hq => hzc q (hQT hq)⟩
  apply (mem_faithfulLocalComponents_iff_module T hE).mpr
  refine ⟨hI,?_⟩
  intro he
  have hs := signalizerModule_le_intrinsicModule I Q (mem_L_isPPerfect hI)
    (le_sup_left.trans hJQ) hIQ hcomm
  rw [signalizerModule_eq_commutator_omegaCenter,he] at hs
  apply hm
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  exact bot_unique ((commutator_mono le_rfl hZ).trans hs)

private theorem exists_central_seed (T : Sylow 2 G) {V : Subgroup G}
    (hVT : V ≤ (T : Subgroup G)) (hn : (T : Subgroup G) ≤ normalizer (V : Set G))
    [IsElementaryAbelian 2 V] (hV : V ≠ ⊥) :
    ∃ z : G, z ∈ V ∧ z ≠ 1 ∧ z ∈ omegaOneCenterAmbient (T : Subgroup G) := by
  let B := V.subgroupOf (T : Subgroup G)
  let : B.Normal := normal_subgroupOf_of_le_normalizer hn
  have hB : B ≠ ⊥ := by
    intro he
    apply hV
    have hh := congrArg (map (T : Subgroup G).subtype) he
    simpa only [B,map_subgroupOf_eq_of_le hVT,Subgroup.map_bot] using hh
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hB
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  obtain ⟨z,hzne,hzc⟩ := exists_nontrivial_center_mem_normal B (p := 2)
  refine ⟨z.val.val,z.property,?_,?_⟩
  · intro he
    exact hzne (Subtype.ext (Subtype.ext he))
  · apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨z.val.property,elemPow_eq_one_of_isElementaryAbelian (p := 2) _ z.property,?_⟩
    intro t ht
    exact congrArg (fun a : T => (a : G)) ((mem_center_iff.mp hzc) ⟨t,ht⟩)

variable {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- A strict first component forces the retained fixed layer to vanish.
Otherwise its normalizer contains both LT and K, contrary to nonsolvable
uniqueness and the strictness of the original component embedding. -/
theorem first_strict_fixed_layer_eq_bot
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) : V ⊓ centralizer (L : Set G) = ⊥ := by
  by_contra hne
  let C := V ⊓ centralizer (L : Set G)
  have htwo : IsPGroup 2 C := T.isPGroup'.to_le (inf_le_left.trans D.le_sylow)
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf S.sylow_normalizes
      (D.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L))).trans
        inf_normalizer_le_normalizer_inf
  have hLC : L ≤ centralizer (C : Set G) := le_centralizer_iff.mp inf_le_right
  have hLTC : L ⊔ (T : Subgroup G) ≤ normalizer (C : Set G) :=
    sup_le (hLC.trans (Subgroup.centralizer_le_normalizer _)) hTC
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.source.simpleQTKE T S.source.maximal_faithful.1
  have hunique : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      L ⊔ (T : Subgroup G) ≤ M → M = normalizer (L : Set G) := by
    simpa only [D.localOrbit_eq] using hu.normalizer_unique
  have hbound := normalizer_le_of_unique_maximalTwoLocal hunique htwo hne hLTC
  have hKC : K ≤ normalizer (C : Set G) :=
    ((subspace_containing_component_centralizes D S f (f.Vi 0) le_rfl hm hfix hK hLK.le).trans
      (centralizer_le (f.centralizer_le_Vi 0))).trans (Subgroup.centralizer_le_normalizer _)
  exact hLK.ne (flag_component_eq_of_le_component_normalizer D S f 0 hm hK hLK.le
    (hKC.trans hbound))

variable
    (m : CFSG.Quasithin.ChapterB.QuasisimpleSource.ActionEquiv D.centralQuotientAction
      (Representation.restrictScalars (k := ZMod 2)
        (Representation.symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m))

/-- In the fixed-free symplectic marking, the second residual moves the
actual Sylow omega-center. A nonzero central seed lies in the first flag
line, so simultaneous centralization would contradict residual generation. -/
theorem sp4_second_moves_sylow_center
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hfaith : V ⊓ centralizer (L : Set G) = ⊥) :
    ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ centralizer (f.Li 1 : Set G) := by
  have he (i : Fin 3) : f.space i = (LocalGeometry.Sp4.flag m S).space i :=
    LocalGeometry.Sp4.flag_inner_unique m S i (f.space i) (f.dimension i)
      (inf_le_left.trans (f.invariant i))
  have hv (i : Fin 3) : f.Vi i = (LocalGeometry.Sp4.flag m S).Vi i :=
    congrArg (Coordinates.preimage (.sp4 m)) (he i)
  have hr (i : Fin 2) : f.Li i = (LocalGeometry.Sp4.flag m S).Li i :=
    congrArg (localResidual L) (hv i.castSucc)
  have hgen : f.Li 0 ⊔ f.Li 1 = L := by
    rw [hr 0,hr 1]
    exact LocalGeometry.Sp4.flag_Li_sup m S S.nonbinary
  let := D.elementary
  obtain ⟨z,hzV,hzne,hzZ⟩ := exists_central_seed T D.le_sylow S.sylow_normalizes D.ne_bot
  have hzfirst : z ∈ f.Vi 0 := by
    rw [hv 0]
    apply (LocalGeometry.Sp4.mem_preimage_succ_iff m 0 ⟨z,hzV⟩).mpr
    intro l hl
    have hz := (mem_omegaOneCenterAmbient_iff _ _).mp hzZ
    have hc : (l : G) * z * (l : G)⁻¹ * z⁻¹ = 1 := by
      rw [hz.2.2 l hl]
      group
    rw [hc]
    exact one_mem _
  intro hm
  have hzL : z ∈ centralizer (L : Set G) := by
    have hzA : f.Li 0 ≤ centralizer ({z} : Set G) := by
      intro a ha
      exact mem_centralizer_singleton_iff.mpr (hfix ha z hzfirst).symm
    have hzB : f.Li 1 ≤ centralizer ({z} : Set G) := by
      intro b hb
      exact mem_centralizer_singleton_iff.mpr (hm hzZ b hb)
    intro l hl
    exact (mem_centralizer_singleton_iff.mp ((sup_le hzA hzB) (hgen.symm ▸ hl)))
  exact hzne (mem_bot.mp (hfaith ▸ (show z ∈ V ⊓ centralizer (L : Set G) from ⟨hzV,hzL⟩)))

/-- Sylow-center movement makes the literal local join faithful, without
a model recognition or an assumed natural action on that join. -/
theorem sp4_triangle_join_faithful
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hfaith : V ⊓ centralizer (L : Set G) = ⊥)
    {K₀ : Subgroup G} (hI : K₀ ⊔ f.Li 1 ∈ Chapter1.L G T)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G)) :
    K₀ ⊔ f.Li 1 ∈ MainForward.faithfulLocalComponents T := by
  apply local_faithful_of_sylow_center_movement T (S.source.simpleQTKE.evenCharacteristic T) hI
    ((le_inf hTK₀ (f.sylow_normalizes_Li 1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup K₀ (f.Li 1)))
  intro h
  exact sp4_second_moves_sylow_center D S m f hfix hfaith
    (h.trans (centralizer_le (show f.Li 1 ≤ K₀ ⊔ f.Li 1 from le_sup_right)))

/-- In the actual strict symplectic triangle, the common-normal construction
produces a faithful local component, with the original Cartan and three-ranks.
The fixed-free condition is proved from strictness, not supplied by the caller.
The source amalgam argument still has to supply Q. -/
theorem sp4_triangle_join_faithful_of_common_normal
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    Source.NormalComponentIn ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)) (K₀ ⊔ f.Li 1) ∧
      (K₀ ⊔ f.Li 1) ∈ Chapter1.L G T ∧ (K₀ ⊔ f.Li 1) ∈ Chapter1.He G ∧
      (K₀ ⊔ f.Li 1) ∈ MainForward.faithfulLocalComponents T ∧
      X ≤ K₀ ⊔ f.Li 1 ∧ primeRank 3 (K₀ ⊔ f.Li 1 : Subgroup G) = 2 ∧
      primeRank 3 ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) = 2 := by
  obtain ⟨hI,hIL,hIH,_⟩ := triangle_join_component_of_common_normal_projective
    D S f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  have hfaith := first_strict_fixed_layer_eq_bot D S f hm₁ hfix hK.1 hLK
  have hf := sp4_triangle_join_faithful D S m f hfix hfaith hIL hTK₀
  obtain ⟨hr,hrq⟩ := sp4_triangle_join_three_rank D S m f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp hQ hQT hKQ hLQ
  exact ⟨hI,hIL,hIH,hf,sp4_triangle_cartan_le_join D S m f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp,hr,hrq⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
