module
public import Glauberman.PushingUpSL2DegreeGaps
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.GroupTheory.SubgroupTransport.SharpGap
/-!
# Original-degree Niles sharp gap and class bound

The Borel theorem for the original SL₂ quotient makes an escaping
subgroup of either Sylow generate with the opposite Sylow. Applying the
literal backward-shift argument in both orientations proves 5v ≤ 2k.
The previously constructed exact gap centralizers then place the derived
subgroup centrally modulo the full Sylow center, giving class at most three.

Source: Niles, *Pushing-up in finite groups* (1979), Lemmas 5.3(d)--5.4,
pp.50--51. Neither the degree nor the full central attachments are changed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- In an original SL₂ cover, an escaping subgroup of one Sylow generates
with the other. A proper join lies in the Borel; its two-group structure
would then force containment in the opposite Sylow. -/
theorem sl2_sylow_escaping_join
    (e : (G ⧸ pCore 2 G) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (S T : Sylow 2 G) (U : Subgroup G) (hUS : U ≤ (S : Subgroup G))
    (hUT : ¬ U ≤ (T : Subgroup G)) : U ⊔ (T : Subgroup G) = ⊤ := by
  by_contra hproper
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 G := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hn := Matrix.SpecialLinearGroup.proper_overgroup_le_sylow_normalizer_of_two_kernel
    q hq T (hk ▸ pCore_isPGroup.le_sylow_of_normal T) (U ⊔ (T : Subgroup G)) le_sup_right hproper
  have hp := (S.isPGroup'.to_le hUS).to_sup_of_normal_right' T.isPGroup' (le_sup_left.trans hn)
  exact hUT (sup_eq_right.mp (T.is_maximal' hp le_sup_right))

/-- Sharp first-gap inequality for the same marked original-degree pair.
Both endpoint alternatives are discharged using the original SL₂ quotient. -/
theorem sl2_gap_sharp
    (e : (G ⧸ pCore 2 G) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (S T : Sylow 2 G) (φ : (S : Subgroup G) ≃* (T : Subgroup G))
    {q v k : ℕ} (hnum : NumericalPairAt q (S : Subgroup G) (T : Subgroup G) φ)
    (hinter : (S : Subgroup G) ⊓ (T : Subgroup G) = pCore 2 G)
    (hv : 0 < v) (hk : 2*v < k) (hkw : k < 3*v)
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hshort : ∀ a b : ℕ, b ≤ 3*v → b < a+2*v →
      IsElementaryAbelian 2 (intervalDiagram φ (3*v) a b))
    (hzS : centerIn (S : Subgroup G) = intervalDiagram φ (3*v) v (2*v-1))
    (hzT : centerIn (T : Subgroup G) = intervalDiagram φ (3*v) (v+1) (2*v))
    (hzQ : centerIn (pCore 2 G) = intervalDiagram φ (3*v) v (2*v))
    (htwice : ∀ i : ℕ, i ≤ v →
      ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) (i+2*v) (i+2*v)⁆ ≤
        intervalDiagram φ (3*v) (i+v) (i+v))
    (hpoint : ∀ i : ℕ, i ≤ v → let X := intervalDiagram φ (3*v)
      PointCommutatorCovering (X i i) (X (i+1) (i+1))
        (X (i+2*v) (i+2*v)) (X (i+2*v-1) (i+2*v-1)) (X (i+v) (i+v)) (X (i+v+1) (i+v+1)) ∧
      PointCommutatorCovering (X i i) (X (i+1) (i+1))
        (X (i+2*v) (i+2*v)) (X (i+2*v-1) (i+2*v-1)) (X (i+v) (i+v)) (X (i+v-1) (i+v-1)))
    (hgap : ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ 3*v → j < i+k →
      ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) j j⁆ ≤ centerIn (T : Subgroup G))
    (hkernel : centralizer (intervalDiagram φ (3*v) v (2*v) : Set G) = pCore 2 G)
    (hex : ∃ i : ℕ, 1 ≤ i ∧ i+k ≤ 3*v ∧
      ¬ ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) (i+k) (i+k)⁆ ≤ centerIn (T : Subgroup G)) :
    5*v ≤ 2*k := by
  classical
  have hneT : ¬ (T : Subgroup G) ≤ (S : Subgroup G) := by
    intro hle
    have hi := hnum.index_right
    have he : ((S : Subgroup G) ⊓ (T : Subgroup G)).relIndex (T : Subgroup G) = 1 :=
      relIndex_eq_one.mpr (le_inf hle le_rfl)
    rw [he] at hi
    have := hnum.nontrivial_index
    omega
  have hneS : ¬ (S : Subgroup G) ≤ (T : Subgroup G) := by
    intro hle
    exact hneT (le_of_eq (S.is_maximal' T.isPGroup' hle))
  have hnV : (⊤ : Subgroup G) ≤ normalizer (intervalDiagram φ (3*v) v (2*v) : Set G) := by
    rw [←hzQ]
    exact normalizes_centerIn (show (⊤ : Subgroup G) ≤ normalizer (pCore 2 G : Set G) from
      le_normalizer_of_normal)
  have hkerS : (S : Subgroup G) ⊓ centralizer (intervalDiagram φ (3*v) v (2*v) : Set G) ≤
      (S : Subgroup G) ⊓ (T : Subgroup G) := by rw [hkernel,hinter]; exact inf_le_right
  have hl := intervalDiagram_gap_left_bound φ v k hk hkw hnum.normal_left hnum.normal_right
    hneT hgen hshort hzT htwice (fun m hm => (hpoint m hm).2) hgap hkerS hnV
    (sl2_sylow_escaping_join e S T)
  by_contra hbad
  have hleft : ⁅intervalDiagram φ (3*v) 1 1,intervalDiagram φ (3*v) (k+1) (k+1)⁆ ≤
      intervalDiagram φ (3*v) (v+1) (3*v) := by
    by_contra hh
    exact hbad (hl hh)
  have hgenR : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ.symm a (b+1) ⊔ intervalCell φ.symm (a+1) b = intervalCell φ.symm a b := by
    intro a b hab
    simpa only [intervalCell_symm,sup_comm] using hgen b a (by omega)
  have hzR : centerIn (S : Subgroup G) = intervalDiagram φ.symm (3*v) (v+1) (2*v) := by
    rw [intervalDiagram_symm φ (3*v) (v+1) (2*v) (by omega)]
    simpa only [show 3*v-2*v=v by omega,show 3*v-(v+1)=2*v-1 by omega] using hzS
  have htwiceR : ∀ i : ℕ, i ≤ v →
      ⁅intervalDiagram φ.symm (3*v) i i,intervalDiagram φ.symm (3*v) (i+2*v) (i+2*v)⁆ ≤
        intervalDiagram φ.symm (3*v) (i+v) (i+v) := by
    intro i hi
    rw [intervalDiagram_symm φ (3*v) i i (by omega),
      intervalDiagram_symm φ (3*v) (i+2*v) (i+2*v) (by omega),
      intervalDiagram_symm φ (3*v) (i+v) (i+v) (by omega),commutator_comm]
    simpa only [show 3*v-(i+2*v)=v-i by omega,
      show 3*v-i=v-i+2*v by omega,show 3*v-(i+v)=v-i+v by omega] using
      htwice (v-i) (by omega)
  have hVR : intervalDiagram φ.symm (3*v) v (2*v) = intervalDiagram φ (3*v) v (2*v) := by
    simp only [intervalDiagram,intervalCell_symm,show 3*v-2*v=v by omega]
  have hr := intervalDiagram_gap_left_bound φ.symm v k hk hkw
    (by simpa only [inf_comm] using hnum.normal_right)
    (by simpa only [inf_comm] using hnum.normal_left) hneS hgenR
    (intervalDiagram_short_symm φ v hv hshort) hzR htwiceR
    (fun m hm => intervalDiagram_point_covering_reverse φ.symm v hv
      (by simpa only [MulEquiv.symm_symm,Nat.zero_add] using (hpoint 0 (by omega)).1) m hm)
    (intervalDiagram_gap_central_symm φ v k hv hzS hzT hgap)
    (by rw [hVR,hkernel,←hinter]; exact le_inf inf_le_left (inf_le_right.trans inf_le_left))
    (by rw [hVR]; exact hnV) (sl2_sylow_escaping_join e T S)
  have hleftR : ⁅intervalDiagram φ.symm (3*v) 1 1,intervalDiagram φ.symm (3*v) (k+1) (k+1)⁆ ≤
      intervalDiagram φ.symm (3*v) (v+1) (3*v) := by
    by_contra hh
    exact hbad (hr hh)
  have hright := intervalDiagram_reflected_gap_right_bound φ v k hk (by omega) hleftR
  exact (intervalDiagram_gap_endpoint_escape φ v k hk hkw hzT hex).elim
    (fun hh => hh hleft) (fun hh => hh hright)
/-- The full original-degree Niles Sylow has class at most three.
The numerical premise in the earlier conditional API is now discharged. -/
theorem original_sl2_class_three
    (e : (G ⧸ pCore 2 G) ≃* Matrix.SpecialLinearGroup (Fin 2) F) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) :
    (S : Subgroup G).lowerCentralSeries 3 = ⊥ ∧ Group.nilpotencyClass S ≤ 3 := by
  obtain ⟨g,hg,hgen,hinter,hnum,v,hv,hj,hshort,hzs,hzt,hzq,hzg,htwice,hpoint,hbranch⟩ :=
    original_sl2_gap_diagram e hn hF S α hfit hno
  let T := S.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  let φ := twistedConjugacy (S : Subgroup G) α g
  have hcT : (T : Subgroup G).lowerCentralSeries 3 = ⊥ := by
    rcases hbranch with hc | ⟨k,hk,hkw,hex,hgap,_,_,_,_,_,_,_,_,hclass⟩
    · have htwo : (T : Subgroup G).lowerCentralSeries 2 = ⊥ := by
        simp only [Subgroup.lowerCentralSeries_succ,Subgroup.lowerCentralSeries_zero]
        exact commutator_eq_bot_iff_le_centralizer.mpr (hc.trans inf_le_right)
      rw [Subgroup.lowerCentralSeries_succ,htwo,commutator_bot_left]
    · have hω := hnum.omegaCenters_eq_centers.2.2
      rw [hinter] at hω
      have hC := sl2_core_omega_centralizer e hn hF S hfit hno.noCharacteristicNormal
      rw [hω,hzq] at hC
      have hsharp := sl2_gap_sharp e S T φ hnum hinter hv hk hkw hj hshort
        hzs hzt hzq htwice hpoint hgap hC hex
      exact (hclass hsharp).2
  have hcS : (S : Subgroup G).lowerCentralSeries 3 = ⊥ := by
    apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [Subgroup.map_lowerCentralSeries,Subgroup.map_bot]
    exact hcT
  have hnil : Group.IsNilpotent S := S.isPGroup'.isNilpotent
  let _ := hnil
  refine ⟨hcS,Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp ?_⟩
  apply map_injective (S : Subgroup G).subtype_injective
  rw [Subgroup.top_subtype_lowerCentralSeries,Subgroup.map_bot]
  exact hcS

end Glauberman
