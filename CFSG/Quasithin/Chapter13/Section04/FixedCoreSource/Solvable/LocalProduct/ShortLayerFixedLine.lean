module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ShortLayerComparison
public import Theory.Representation.BinaryPermutation.SixCoreFixedLayer
/-!
# The fixed-line contradiction for the larger kernel

A common normalizer of L and V which centralizes [V,L₁] acts on the
marked five-space as a linear map normalizing the actual A₆ action.
The constant line is fixed because it has order two. The six-letter
orbit calculation forces that line into any subgroup containing [V,L₁]
and the normalizer's displacements.

Apply this to a moving element of Vᵍ. The comparison theorem identifies
the two residual layers, so [V,L₁] lies in V∩Vᵍ and Vᵍ centralizes it.
The original two-core normalizes both five-spaces, putting every
commutator in the intersection. Earlier fusion excludes the fixed line
there. This proves [J(R₁),V_H]≠1 in the larger-kernel short-block branch.

The normality input is proved from earlier 13.3.9; the covered-only
13.2.2(9) normalizer bound is not used. Earlier fusion, the literal
residual-section Sylow placement and V≤J(R₁) remain explicit genuine
source inputs. Their final discharge belongs to qt-d-1341-fixed-core-source
and its existing producers. The original R₁ identification, C₃ geometry
and ambient fusion remain with qt-d-1341-solvable-source.
Source: Aschbacher–Smith 13.4.8, printed p.904.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Stellmacher Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- A moving common normalizer which centralizes the original residual layer
forces the fixed line into any subgroup containing that layer and its
commutators with V. -/
theorem fixed_le_of_centralizing_residual_layer
    (D : ChosenModule T L V) (m : CoreMarking D) (z : V)
    (hzL : z.val ∉ centralizer (L : Set G))
    (N : Subgroup G)
    (hWN : ⁅V,firstCentralizerResidual L z.val⁆ ≤ N)
    (n : G) (hnV : n ∈ normalizer (V : Set G))
    (hnL : n ∈ normalizer (L : Set G))
    (hnW : n ∈ centralizer ((⁅V,firstCentralizerResidual L z.val⁆ : Subgroup G) : Set G))
    (hnc : n ∉ centralizer (V : Set G))
    (hnN : ∀ v : V, n*v.val*n⁻¹*v.val⁻¹ ∈ N) :
    V ⊓ centralizer (L : Set G) ≤ N := by
  classical
  let C := L ⊓ centralizer ({z.val} : Set G)
  let w := (m.coordinate z).toAdd
  let U : Submodule (ZMod 2) (BinaryPermutation.core (Fin 6)) :=
    AddSubgroup.toZModSubmodule 2
      ((N.subgroupOf V).map m.coordinate.toMonoidHom).toAddSubgroup'
  have hmem (v : V) : (m.coordinate v).toAdd ∈ U ↔ v.val ∈ N := by
    change m.coordinate v ∈ (N.subgroupOf V).map m.coordinate.toMonoidHom ↔ _
    exact mem_map_iff_mem (f := m.coordinate.toMonoidHom) m.coordinate.injective
  let β := V.normalizerMonoidHom ⟨n,hnV⟩
  let c := m.coordinate.symm.trans (β.trans m.coordinate)
  let u := (AddMonoidHom.toMultiplicative.symm c.toMonoidHom).toZModLinearMap 2
  have hu (v : V) : u (m.coordinate v).toAdd = (m.coordinate (β v)).toAdd := by
    change (m.coordinate (β (m.coordinate.symm (m.coordinate v)))).toAdd = _
    rw [MulEquiv.symm_apply_apply]
  have hfix : ¬ ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a w = w := by
    intro h
    exact hzL ((m.mem_fixed_iff z).mpr
      ((BinaryPermutation.core_fixed_iff_constant (by simp) w).mp h))
  have hβfix (v : V) (hv : v.val ∈ ⁅V,firstCentralizerResidual L z.val⁆) : β v = v := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hnW v.val hv).symm
  obtain ⟨f,hf,_,he⟩ := component_centralizer_action D m z
  have hdisp : ∀ x : BinaryPermutation.SixCoreStabilizer.stabilizer w,
      x ∈ primeToResidual 3 (BinaryPermutation.SixCoreStabilizer.stabilizer w) →
      ∀ v : BinaryPermutation.core (Fin 6),
      ∃ t : V, t.val ∈ ⁅V,firstCentralizerResidual L z.val⁆ ∧
        (m.coordinate t).toAdd =
          BinaryPermutation.alternatingCoreRepresentation (Fin 6) x.val v-v := by
    intro x hx v
    obtain ⟨a,ha,hax⟩ := (show x ∈ (primeToResidual 3 C).map f by
      rwa [map_primeToResidual_of_surjective 3 f hf])
    have haA : a.val ∈ firstCentralizerResidual L z.val := by
      rw [firstCentralizerResidual_eq]
      exact mem_map_of_mem C.subtype ha
    let v₀ := m.coordinate.symm (Multiplicative.ofAdd v)
    let t : V := V.normalizerMonoidHom ⟨a.val,D.normalizes a.property.1⟩ v₀ * v₀⁻¹
    refine ⟨t,?_,?_⟩
    · rw [commutator_comm]
      exact commutator_mem_commutator haA v₀.property
    · change (m.coordinate (_ * _)).toAdd = _
      rw [map_mul,map_inv,toAdd_mul,toAdd_inv,← sub_eq_add_neg,he,hax]
      simp only [v₀,MulEquiv.apply_symm_apply,toAdd_ofAdd]
  have hUdisp : ∀ x : BinaryPermutation.SixCoreStabilizer.stabilizer w,
      x ∈ primeToResidual 3 (BinaryPermutation.SixCoreStabilizer.stabilizer w) →
      ∀ v : BinaryPermutation.core (Fin 6),
        BinaryPermutation.alternatingCoreRepresentation (Fin 6) x.val v-v ∈ U := by
    intro x hx v
    obtain ⟨t,ht,he⟩ := hdisp x hx v
    rw [← he]
    exact (hmem t).mpr (hWN ht)
  have hufix : ∀ x : BinaryPermutation.SixCoreStabilizer.stabilizer w,
      x ∈ primeToResidual 3 (BinaryPermutation.SixCoreStabilizer.stabilizer w) →
      ∀ v : BinaryPermutation.core (Fin 6),
        u (BinaryPermutation.alternatingCoreRepresentation (Fin 6) x.val v-v) =
          BinaryPermutation.alternatingCoreRepresentation (Fin 6) x.val v-v := by
    intro x hx v
    obtain ⟨t,ht,he⟩ := hdisp x hx v
    rw [← he,hu,hβfix t ht]
  have hud : u BinaryPermutation.sixCoreConstant = BinaryPermutation.sixCoreConstant := by
    let d := m.coordinate.symm (Multiplicative.ofAdd BinaryPermutation.sixCoreConstant)
    have hdcoord : (m.coordinate d).toAdd = BinaryPermutation.sixCoreConstant := by
      simp only [d,MulEquiv.apply_symm_apply,toAdd_ofAdd]
    have hd : d.val ∈ V ⊓ centralizer (L : Set G) := ⟨d.property,
      (m.mem_fixed_iff d).mpr ((BinaryPermutation.core_fixed_iff_constant (by simp) _).mp
        (by rw [hdcoord]; exact BinaryPermutation.sixCoreConstant_fixed))⟩
    have hnfix : n ∈ normalizer (V ⊓ centralizer (L : Set G) : Set G) :=
      inf_normalizer_le_normalizer_inf ⟨hnV,normalizer_le_normalizer_centralizer L hnL⟩
    have hnd := normalizer_le_centralizer_of_card_two _ m.card_fixed hnfix d.val hd
    have hβd : β d = d := Subtype.ext (mul_inv_eq_iff_eq_mul.mpr hnd.symm)
    rw [← hdcoord,hu,hβd]
  let π : L →* alternatingGroup (Fin 6) :=
    m.quotient.toMonoidHom.comp (QuotientGroup.mk' _)
  have hπ : Function.Surjective π :=
    m.quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  have hun : ∀ a : alternatingGroup (Fin 6), ∃ b : alternatingGroup (Fin 6),
      ∀ v : BinaryPermutation.core (Fin 6),
        u (BinaryPermutation.alternatingCoreRepresentation (Fin 6) a v) =
          BinaryPermutation.alternatingCoreRepresentation (Fin 6) b (u v) := by
    intro a
    obtain ⟨l,rfl⟩ := hπ a
    let l' := L.normalizerMonoidHom ⟨n,hnL⟩ l
    refine ⟨π l',fun v => ?_⟩
    let v₀ := m.coordinate.symm (Multiplicative.ofAdd v)
    have hvcoord : (m.coordinate v₀).toAdd = v := by
      simp only [v₀,MulEquiv.apply_symm_apply,toAdd_ofAdd]
    have hconj : β (V.normalizerMonoidHom ⟨l.val,D.normalizes l.property⟩ v₀) =
        V.normalizerMonoidHom ⟨l'.val,D.normalizes l'.property⟩ (β v₀) := by
      apply Subtype.ext
      change n*(l.val*v₀.val*l.val⁻¹)*n⁻¹ =
        (n*l.val*n⁻¹)*(n*v₀.val*n⁻¹)*(n*l.val*n⁻¹)⁻¹
      group
    have hleft := m.equivariant l v₀
    have hright := m.equivariant l' (β v₀)
    change _ = BinaryPermutation.alternatingCoreRepresentation (Fin 6) (π l) _ at hleft
    change _ = BinaryPermutation.alternatingCoreRepresentation (Fin 6) (π l') _ at hright
    rw [← hvcoord,← hleft,hu,hconj,hright,← hu]
  have hune : ∃ v : BinaryPermutation.core (Fin 6), u v ≠ v := by
    by_contra! hh
    apply hnc
    intro v hv
    let v₀ : V := ⟨v,hv⟩
    have hβ : β v₀ = v₀ := m.coordinate.injective (Multiplicative.toAdd.injective
      ((hu v₀).symm.trans (hh _)))
    have hval := congrArg Subtype.val hβ
    exact (mul_inv_eq_iff_eq_mul.mp (show n*v*n⁻¹=v from hval)).symm
  have hum : ∀ v : BinaryPermutation.core (Fin 6), u v-v ∈ U := by
    intro v
    let v₀ := m.coordinate.symm (Multiplicative.ofAdd v)
    have hvcoord : (m.coordinate v₀).toAdd = v := by
      simp only [v₀,MulEquiv.apply_symm_apply,toAdd_ofAdd]
    have hh := (hmem (β v₀ * v₀⁻¹)).mpr (hnN v₀)
    change (m.coordinate (_ * _)).toAdd ∈ U at hh
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,← sub_eq_add_neg,← hu,hvcoord] at hh
    exact hh
  have hconstant := BinaryPermutation.SixCoreFixedLayer.constant_mem_of_fixed_residual_layer
    w hfix U u hUdisp hufix hud hun hune hum
  intro v hv
  let v₀ : V := ⟨v,hv.1⟩
  apply (hmem v₀).mp
  have hfixed := (BinaryPermutation.core_fixed_iff_constant (by simp) (m.coordinate v₀).toAdd).mpr
    ((m.mem_fixed_iff v₀).mp hv.2)
  rcases (BinaryPermutation.sixCore_fixed_iff _).mp hfixed with hzero | hconst
  · rw [hzero]; exact U.zero_mem
  · rwa [hconst]

/-- The moving-layer comparison and fixed-line orbit calculation discharge
the centralizing Thompson alternative in the actual larger-kernel short-block
branch. Earlier residual classification, fusion and Sylow placement are the
only remaining earlier-source inputs. -/
theorem centralizer_larger_thompson_noncentral_of_short_block
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hlarge : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) ≠
      pCore 2 (centralizer ({z.val} : Set G)))
    (R : Subgroup G) (hRT : R ≤ T)
    (S : Sylow 2 (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
        (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))))))
    (hR : ((S : Subgroup _).map (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
        (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))))).subtype).map
          (centralizer ({z.val} : Set G)).subtype = R)
    (hVJ : V ≤ elementaryAbelianMaxJ R)
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3)) :
    ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z.val : Set G) := by
  classical
  intro hJ
  obtain ⟨g,hg,hgQ,_,hWN,hW,hcomm,hne,hfixed⟩ :=
    centralizer_larger_short_block_equal_layers h₀ h structural D m hb z hz hzL
      hlarge R hRT S hR hVJ hJ hout hfusion h1339
  have hn : ∃ n ∈ V.conjBy g, n ∉ centralizer (V : Set G) := by
    by_contra! hall
    exact hne (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hall))
  obtain ⟨n,hn,hnc⟩ := hn
  have hTH : (T : Subgroup G) ≤ centralizer ({z.val} : Set G) :=
    original_sylow_le_centralizer hz
  have hQT : (centralizer ({z.val} : Set G)).pCoreIn 2 ≤ T := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow _ (T.subtype hTH)
  have hnL := D.sylow_normalizes_component (hQT (hgQ hn))
  have hnV := normalizer_component_le_module h structural D m hnL
  have hline := fixed_le_of_centralizing_residual_layer D m z hzL
    (V ⊓ V.conjBy g) hWN n hnV hnL (hW hn) hnc (by
      intro v
      apply hcomm
      rw [commutator_comm]
      exact commutator_mem_commutator hn v.property)
  exact hfixed (hline.trans inf_le_right)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
