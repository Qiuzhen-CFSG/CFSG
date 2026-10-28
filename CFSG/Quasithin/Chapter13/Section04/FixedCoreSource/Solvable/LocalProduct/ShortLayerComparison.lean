module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ShortConjugates
public import Theory.Representation.BinaryPermutation.SixCoreQuadraticResidual
/-!
# Comparison of the two original residual layers

An abelian subgroup B of the literal L₁=O^{3′}(C_L(z)), normalized by
both L₁ and V, centralizes V. The actual stabilizer action transports
mixed commutators to the six-letter core, where two cubic conjugates
detect every nonidentity residual actor.

For B=[V,L₁]ᵍ=[Vᵍ,L₁], normality of L₁ in H and normalization of Vᵍ
by O₂(H) supply these hypotheses. The short-block identity [C_T(V),L]≤V
then puts B in V, and residual idempotence puts B in [V,L₁]. Conjugation
preserves order, proving equality of the two original layers.

The final source application retains the moving conjugate and the
fixed-line exclusion from earlier fusion control. ShortLayerFixedLine
applies the orbit calculation to force that line into the intersection
and finish the contradiction. The original R₁ placement, C₃ geometry
and ambient fusion remain with qt-d-1341-solvable-source. The genuine earlier inputs retain final
discharge with qt-d-1341-fixed-core-source and its existing producers.
Source: Aschbacher–Smith 13.4.8, printed p.904, the paragraph beginning
“Suppose that L₁ is normal in H”.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Stellmacher Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- An abelian subgroup of the literal cubic residual, normalized both by
that residual and by the original five-space, centralizes the five-space. -/
theorem firstCentralizerResidual_abelian_normalized_centralizes
    (D : ChosenModule T L V) (m : CoreMarking D) (z : V)
    (hzL : z.val ∉ centralizer (L : Set G))
    (B : Subgroup G) [IsMulCommutative B]
    (hBA : B ≤ firstCentralizerResidual L z.val)
    (hAB : firstCentralizerResidual L z.val ≤ normalizer (B : Set G))
    (hVB : V ≤ normalizer (B : Set G)) : B ≤ centralizer (V : Set G) := by
  let C := L ⊓ centralizer ({z.val} : Set G)
  let w := (m.coordinate z).toAdd
  obtain ⟨f,hf,_,he⟩ := component_centralizer_action D m z
  have hfix : ¬ ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a w = w := by
    intro h
    exact hzL ((m.mem_fixed_iff z).mpr
      ((BinaryPermutation.core_fixed_iff_constant (by simp) w).mp h))
  intro x hx v hv
  obtain ⟨c,hc,hcx⟩ := (show x ∈ (primeToResidual 3 C).map C.subtype by
    simpa only [firstCentralizerResidual_eq] using hBA hx)
  change c.val = x at hcx
  have hfc : f c ∈ primeToResidual 3 (BinaryPermutation.SixCoreStabilizer.stabilizer w) := by
    rw [← map_primeToResidual_of_surjective 3 f hf]
    exact mem_map_of_mem f hc
  have hfone : f c = 1 :=
    BinaryPermutation.SixCoreQuadraticResidual.eq_one_of_conjugate_quadratic w hfix (f c) hfc (by
      intro y hy u
      obtain ⟨d,hd,hdy⟩ := (show y ∈ (primeToResidual 3 C).map f by
        rwa [map_primeToResidual_of_surjective 3 f hf])
      have hdA : d.val ∈ firstCentralizerResidual L z.val := by
        rw [firstCentralizerResidual_eq]
        exact mem_map_of_mem C.subtype hd
      have hcB : c.val ∈ B := hcx.symm ▸ hx
      let k : C := MulAut.conj d c
      have hkB : k.val ∈ B := le_normalizer_iff.mp hAB d.val hdA c.val hcB
      have hfk : (f k).val = MulAut.conj y.val (f c).val := by
        change (f (d*c*d⁻¹)).val = _
        simp only [map_mul,map_inv,hdy,MulAut.conj_apply]
        rfl
      let u₀ := m.coordinate.symm (Multiplicative.ofAdd u)
      let t : V := V.normalizerMonoidHom ⟨k.val,D.normalizes k.property.1⟩ u₀ * u₀⁻¹
      have htB : t.val ∈ B :=
        le_normalizer_iff_commutator_le_left.mp hVB
          (commutator_mem_commutator hkB u₀.property)
      have hct : Commute c.val t.val :=
        congrArg Subtype.val ((isMulCommutative_iff.mp (inferInstance : IsMulCommutative B))
          (⟨c.val,hcB⟩ : B) ⟨t.val,htB⟩)
      have htc : V.normalizerMonoidHom ⟨c.val,D.normalizes c.property.1⟩ t = t := by
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr hct
      have htcoord : (m.coordinate t).toAdd =
          BinaryPermutation.alternatingCoreRepresentation (Fin 6) (f k).val u - u := by
        change (m.coordinate (_ * _)).toAdd = _
        rw [map_mul,map_inv,toAdd_mul,toAdd_inv,← sub_eq_add_neg,he]
        simp only [u₀,MulEquiv.apply_symm_apply,toAdd_ofAdd]
      have hh := he c t
      rw [htc,htcoord,hfk] at hh
      exact hh.symm)
  let v₀ : V := ⟨v,hv⟩
  have hh := he c v₀
  rw [hfone] at hh
  have heq : V.normalizerMonoidHom ⟨c.val,D.normalizes c.property.1⟩ v₀ = v₀ := by
    apply m.coordinate.injective
    apply Multiplicative.toAdd.injective
    simpa only [OneMemClass.coe_one,map_one,Module.End.one_apply] using hh
  have hval := congrArg Subtype.val heq
  simpa only [hcx] using
    (mul_inv_eq_iff_eq_mul.mp (show c.val * v * c.val⁻¹ = v from hval)).symm

/-- The two original moved layers coincide whenever the conjugate five-space
is normalized by O₂(H) and the literal residual is normal in H. -/
theorem centralizer_short_block_conjugate_residual_layer_eq
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVQ : V ≤ (centralizer ({z.val} : Set G)).pCoreIn 2)
    (hnormal : centralizer ({z.val} : Set G) ≤
      normalizer (firstCentralizerResidual L z.val : Set G))
    (g : G) (hg : g ∈ centralizer ({z.val} : Set G))
    (hQn : (centralizer ({z.val} : Set G)).pCoreIn 2 ≤
      normalizer (V.conjBy g : Set G)) :
    (⁅V,firstCentralizerResidual L z.val⁆ : Subgroup G).conjBy g =
      ⁅V,firstCentralizerResidual L z.val⁆ := by
  let H := centralizer ({z.val} : Set G)
  let A := firstCentralizerResidual L z.val
  let W := ⁅V,A⁆
  let B := W.conjBy g
  have hAL : A ≤ L := (firstCentralizerResidual_le L z.val).trans inf_le_left
  have hAV := hAL.trans D.normalizes
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp hAV
  have hBVg : B ≤ V.conjBy g := map_mono hWV
  let := D.elementary
  let : IsMulCommutative (V.conjBy g) :=
    inferInstanceAs (IsMulCommutative (V.map (MulAut.conj g).toMonoidHom))
  let : IsMulCommutative B := IsMulCommutative.of_setLike_mul_comm
    (fun x hx y hy => setLike_mul_comm (hBVg hx) (hBVg hy))
  obtain ⟨he,hcore,hm,_⟩ := centralizer_short_block_conjugate_residual_layer
    D m hb z hzL hVQ hnormal g hg
  have hBA : B ≤ A := hcore.trans (pCoreIn_le 2 A)
  have hAB : A ≤ normalizer (B : Set G) := by
    change A ≤ normalizer (W.conjBy g : Set G)
    rw [he]
    exact normalizer_commutator_ge_right _ _
  have hVB : V ≤ normalizer (B : Set G) := by
    intro v hv
    apply mem_normalizer_iff_map_conj_eq.mpr
    change B.map (MulAut.conj v).toMonoidHom = B
    change W.conjBy g = ⁅V.conjBy g,A⁆ at he
    change B = ⁅V.conjBy g,A⁆ at he
    have hvV : (V.conjBy g).map (MulAut.conj v).toMonoidHom = V.conjBy g :=
      mem_normalizer_iff_map_conj_eq.mp (hQn (hVQ hv))
    have hvA : A.map (MulAut.conj v).toMonoidHom = A :=
      mem_normalizer_iff_map_conj_eq.mp (hnormal (pCoreIn_le 2 H (hVQ hv)))
    rw [he,map_commutator,hvV,hvA]
  have hBc := firstCentralizerResidual_abelian_normalized_centralizes
    D m z hzL B hBA hAB hVB
  have hnQ : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hBQT : B ≤ T := by
    have hVgQ : V.conjBy g ≤ H.pCoreIn 2 := by
      have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hVQ
      have hq : (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom = H.pCoreIn 2 :=
        mem_normalizer_iff_map_conj_eq.mp (hnQ hg)
      change V.conjBy g ≤ (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom at hh
      rwa [hq] at hh
    have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
    have hQT : H.pCoreIn 2 ≤ T := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using
        pCoreIn_le_sylow H (T.subtype hTH)
    exact (hBVg.trans hVgQ).trans hQT
  have hBV : B ≤ V := hm.symm.le.trans
    ((commutator_mono (le_inf hBQT hBc) hAL).trans
      (sylow_module_centralizer_commutator_le_chosen D hb))
  have hBW : B ≤ W := hm.symm.le.trans (commutator_mono hBV le_rfl)
  apply eq_of_le_of_card_ge hBW
  change Nat.card W ≤ Nat.card (W.map (MulAut.conj g).toMonoidHom)
  rw [card_map_of_injective (MulAut.conj g).injective]

/-- In the actual larger-kernel short-block contradiction, the moving pair
shares the original residual layer. That layer lies in the intersection
and is centralized by the second five-space. -/
theorem centralizer_larger_short_block_equal_layers
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
    (hJ : elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z.val : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3)) :
    let H := centralizer ({z.val} : Set G)
    let W := ⁅V,firstCentralizerResidual L z.val⁆
    ∃ g ∈ H,
      V.conjBy g ≤ H.pCoreIn 2 ∧
      W.conjBy g = W ∧
      W ≤ V ⊓ V.conjBy g ∧
      V.conjBy g ≤ centralizer (W : Set G) ∧
      ⁅V,V.conjBy g⁆ ≤ V ⊓ V.conjBy g ∧
      ⁅V,V.conjBy g⁆ ≠ ⊥ ∧
      ¬ V ⊓ centralizer (L : Set G) ≤ V.conjBy g := by
  obtain ⟨hn,g,hg,hgQ,hnQ,hcomm,hne,hfixed,_⟩ :=
    centralizer_larger_short_block_moving_layers h₀ h structural D m hb z hz hzL
      hlarge R hRT S hR hVJ hJ hout hfusion h1339
  obtain ⟨hc,_,_,_⟩ := centralizer_larger_kernel_local_data h₀ hz
    (fun he => hzL (he ▸ one_mem _)) R hRT S hR
  have hVQ : V ≤ (centralizer ({z.val} : Set G)).pCoreIn 2 := by
    rw [← hc]
    exact le_inf (hVJ.trans (sSup_le fun _ hA => hA.1)) (hVJ.trans hJ)
  have he := centralizer_short_block_conjugate_residual_layer_eq
    D m hb z hz hzL hVQ hn g hg hnQ
  have hWV : ⁅V,firstCentralizerResidual L z.val⁆ ≤ V :=
    le_normalizer_iff_commutator_le_left.mp
      (((firstCentralizerResidual_le L z.val).trans inf_le_left).trans D.normalizes)
  have hWVg : ⁅V,firstCentralizerResidual L z.val⁆ ≤ V.conjBy g := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hWV
    change (⁅V,firstCentralizerResidual L z.val⁆).conjBy g ≤ V.conjBy g at hh
    rwa [he] at hh
  let := D.elementary
  let : IsMulCommutative (V.conjBy g) :=
    inferInstanceAs (IsMulCommutative (V.map (MulAut.conj g).toMonoidHom))
  have hcVg : V.conjBy g ≤ centralizer (V.conjBy g : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  exact ⟨g,hg,hgQ,he,le_inf hWV hWVg,
    hcVg.trans (centralizer_le hWVg),hcomm,hne,hfixed⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
