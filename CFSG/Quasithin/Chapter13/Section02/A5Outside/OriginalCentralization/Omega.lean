module

public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.Thompson
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.CenterFree
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalBorel
public import CFSG.Quasithin.Chapter13.Section05.A5Source.BlockCoordinates
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Saturation
public import Stellmacher.ElementaryAbelianMaxJFixedIntersection

/-!
# The full omega splitting in the moving original A₅ branch

Symmetric-five saturation splits Ω₁Z(J(T)) into its L-fixed part and
its part in V. Each element of Ω₁Z(T) has T-fixed components, since
V intersects C_G(L) trivially. Thus Ω₁Z(T)=V₁ ⊕ C_{Ω₁Z(T)}(L), and
irreducibility gives the original orbit splitting ⟨Ω₁Z(T)^L⟩=V ⊕ C_{Ω₁Z(T)}(L).
The original Borel fixes V₁ and lies in L, so it centralizes all of Ω₁Z(T).

The final application retains the literal L₁=O²(N_L(T∩L)) and derives
its centrality whenever an original outside H moves Ω₁Z(T). No Baumann
normalizer bound, solvability or outside-centralization theorem is assumed.

Source: Aschbacher--Smith 13.2.4(2b), printed p.879, and the earlier
[Z,L₁]=1 input used in 13.2.12 and 13.2.14, pp.881--883.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section06.CentralizerReduction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The local symmetric-five saturation gives the literal alpha splitting. -/
theorem local_alpha_decomposition
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    ChapterB.thompsonAlpha (T : Subgroup G) =
      (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (L : Set G)) ⊔
        (V ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) := by
  let K := L ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
  let := d.reduced.normal
  let := d.reduced.elementary
  have hq := d.localActor_surjective_of_thompson_moves hJ
  let f := d.localModuleCoordinates.symm
  have hk : ∀ v, f v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation (V.subgroupOf K)
        d.localActor hq d.localActor_kernel g v = v := by
    intro v hv _ _
    have hz : v = 0 := f.injective (hv.trans (map_zero f).symm)
    subst v
    exact map_zero _
  have ha := (ChapterC.SymmetricFive.source_alpha_and_saturation S
    (Chapter5.A5Source.local_minimal_parabolic d) (V.subgroupOf K) d.reduced
    d.localActor hq d.localActor_kernel f.toLinearMap f.surjective
    (Chapter5.A5Source.local_full_equivariant d hq) hk
    (Chapter5.A5Source.local_thompson_moves d hJ)).2.1
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup K)).map K.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) :=
    Chapter5.A5Source.local_thompson_image
  have hEmap : (ChapterB.thompsonAlpha (S : Subgroup K)).map K.subtype =
      ChapterB.thompsonAlpha (T : Subgroup G) := by
    change (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup K))).map
      K.subtype = omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup G))
    rw [← omegaOneCenterAmbient_map_injective K.subtype K.subtype_injective,hJmap]
  have hLmap : (pResidual 2 K).map K.subtype = L :=
    ChapterC.Section05.CounterexampleCharacteristic.normal_extension_residual L (T : Subgroup G) d.twoPerfect T.isPGroup' d.normalizes_L
  have he := congrArg (map K.subtype) ha
  rw [Subgroup.map_sup,← map_inf_centralizer_of_injective K.subtype K.subtype_injective,
    ← map_inf_centralizer_of_injective K.subtype K.subtype_injective,hEmap,hLmap,hJmap,
    map_subgroupOf_eq_of_le (d.chosen.le_sylow.trans le_sup_right)] at he
  exact he

/-- T-invariance and the disjoint local summands split the whole Sylow omega-center. -/
theorem omega_decomposition_of_thompson_moves
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    omegaOneCenterAmbient (T : Subgroup G) =
      V₁ ⊔ (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let E := ChapterB.thompsonAlpha (T : Subgroup G)
  let C := E ⊓ centralizer (L : Set G)
  let W := V ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)
  have hE : E = C ⊔ W := local_alpha_decomposition d hJ
  have hWE : W ≤ E := le_sup_right.trans hE.ge
  let : IsElementaryAbelian 2 E := omegaOneCenterAmbient_elementaryAbelian _
  let : CommGroup E := IsMulCommutative.instCommGroup
  have h1Z : V₁ ≤ omegaOneCenterAmbient (T : Subgroup G) := by
    intro v hv
    have hf := d.flag.module_fixed_eq_line.ge hv
    let := d.elementary
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨d.chosen.le_sylow hf.1,elemPow_eq_one_of_isElementaryAbelian v hf.1,hf.2⟩
  apply le_antisymm ?_ (sup_le h1Z inf_le_left)
  intro z hz
  have hzE : z ∈ E := omegaCenter_le_omegaCenter_maxJ _ hz
  have hzsup : (⟨z,hzE⟩ : E) ∈ C.subgroupOf E ⊔ W.subgroupOf E := by
    rw [← subgroupOf_sup inf_le_left hWE,← hE,subgroupOf_self]
    trivial
  obtain ⟨c,hc,v,hv,hcv⟩ := Subgroup.mem_sup.mp hzsup
  have he : (c:G) * (v:G) = z := congrArg E.subtype hcv
  have hvV : (v:G) ∈ V := hv.1
  have hcL : (c:G) ∈ centralizer (L : Set G) := hc.2
  have hvT : (v:G) ∈ centralizer ((T : Subgroup G) : Set G) := by
    intro t ht
    have hvc : t * (v:G) * t⁻¹ ∈ V :=
      (mem_normalizer_iff.mp (d.flag.T_normalizes ht) _).mp hvV
    have hcc : t * (c:G) * t⁻¹ ∈ centralizer (L : Set G) :=
      (mem_normalizer_iff.mp
        (normalizer_le_normalizer_centralizer L (d.normalizes_L ht)) _).mp hcL
    have hp : (t * (c:G) * t⁻¹) * (t * (v:G) * t⁻¹) = (c:G) * (v:G) := by
      calc
        _ = t * ((c:G) * (v:G)) * t⁻¹ := by group
        _ = t * z * t⁻¹ := by rw [he]
        _ = z := mul_inv_eq_iff_eq_mul.mpr
          (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht)
        _ = _ := he.symm
    have hd : (t * (v:G) * t⁻¹) * (v:G)⁻¹ =
        (t * (c:G) * t⁻¹)⁻¹ * (c:G) := by
      apply (eq_inv_mul_iff_mul_eq).mpr
      rw [← mul_assoc,hp,mul_inv_cancel_right]
    have hzero : (t * (v:G) * t⁻¹) * (v:G)⁻¹ = 1 := by
      apply mem_bot.mp
      rw [← d.flag.module.fixed_eq_bot]
      refine ⟨V.mul_mem hvc (V.inv_mem hvV),?_⟩
      rw [hd]
      exact (centralizer (L : Set G)).mul_mem
        ((centralizer (L : Set G)).inv_mem hcc) hcL
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hzero)
  have hv1 : (v:G) ∈ V₁ := d.flag.module_fixed_eq_line.le ⟨hvV,hvT⟩
  have hcZ : (c:G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
    have hm := (omegaOneCenterAmbient (T : Subgroup G)).mul_mem hz
      ((omegaOneCenterAmbient (T : Subgroup G)).inv_mem (h1Z hv1))
    rwa [← he,mul_inv_cancel_right] at hm
  rw [← he]
  exact (sup_comm V₁ _).ge (mul_mem_sup ⟨hcZ,hcL⟩ hv1)

/-- The full omega orbit and its fixed summand in original 13.2.4(2b). -/
theorem omega_orbit_splitting_of_thompson_moves
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L =
      V ⊔ (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
      Disjoint V (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let C := Z ⊓ centralizer (L : Set G)
  have hZ : Z = V₁ ⊔ C := omega_decomposition_of_thompson_moves d hJ
  have hC : L ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp (show C ≤ centralizer (L : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  constructor
  · apply le_antisymm
    · exact conjugateSpanBy_le
        (hZ.le.trans (sup_le_sup (d.flag.one_le_two.trans d.flag.two_le_V) le_rfl))
        ((le_inf d.chosen.normalizes hC).trans
          (normalizer_inf_normalizer_le_normalizer_sup V C))
    · apply sup_le
      · rw [← d.line_span_eq]
        exact conjugateSpanBy_mono (le_sup_left.trans hZ.ge) le_rfl
      · exact inf_le_left.trans (le_conjugateSpanBy Z L)
  · apply disjoint_iff.mpr
    apply bot_unique
    exact (inf_le_inf_left V (show C ≤ centralizer (L : Set G) from inf_le_right)).trans_eq
      d.flag.module.fixed_eq_bot

/-- The full original Borel centralizes the full Sylow omega-center. -/
theorem borel_centralizes_omega_of_thompson_moves
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    ChapterF.Source.borel L (T : Subgroup G) ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  apply le_centralizer_iff.mpr
  rw [omega_decomposition_of_thompson_moves d hJ,d.borel_eq_point_centralizer]
  exact sup_le (le_centralizer_iff.mp inf_le_right)
    (inf_le_right.trans (centralizer_le inf_le_left))

/-- In particular O²(N_L(T∩L)) centralizes the whole omega-center, retaining
both literal subgroup inclusions used in the outside-group argument. -/
theorem borelResidual_centralizes_omega_of_thompson_moves
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    borelResidual T L ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  let N := normalizer ((T : Subgroup G).subgroupOf L : Set L)
  have hN : N.map L.subtype = ChapterF.Source.borel L (T : Subgroup G) := by
    change (normalizer ((T : Subgroup G).subgroupOf L : Set L)).map L.subtype =
      L ⊓ normalizer ((T : Subgroup G) ⊓ L : Set G)
    rw [← inf_subgroupOf_right (T : Subgroup G) L,
      ← subgroupOf_normalizer_eq (show (T : Subgroup G) ⊓ L ≤ L from inf_le_right),
      subgroupOf_map_subtype,inf_comm]
    rfl
  exact (map_mono (f := L.subtype) (map_subtype_le (pResidual 2 N))).trans
    (hN.le.trans (borel_centralizes_omega_of_thompson_moves d hJ))

/-- The actual counterexample branch supplies the earlier Borel-centrality
premise without a Baumann bound or outside-group solvability assumption. -/
theorem borelResidual_centralizes_omega_of_omega_movement
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    borelResidual T L ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
  borelResidual_centralizes_omega_of_thompson_moves d
    (thompson_moves_of_omega_movement d hH hZ)

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
