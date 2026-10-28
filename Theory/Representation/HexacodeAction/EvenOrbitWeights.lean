module

public import Theory.Representation.HexacodeAction.EvenOrbits
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeCounting
public import Theory.Representation.HexacodeAction.PairGeometry
public import Theory.Representation.HexacodeAction.PlaneStabilizer.Planes

/-!
# The two even hexacode orbits are the weight-four and weight-six sets

The actual even action preserves Hamming weight. Its two nonzero orbits
therefore coincide with the two nonzero weight sets, which both occur.
Their already computed cardinalities are 45 and 18. Thus the even-sized
nonzero orbit is precisely the full-weight orbit, retaining the literal
monomial action and its original words.

This is the finite module step used in Aschbacher--Smith12.7.4,
printed pp.839--840. The code, action and weight distribution retain the
ATLAS attribution from the imported sources; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Atlas.Codes
namespace Representation.Hexacode

/-- The original even monomial action preserves the actual code weight. -/
theorem evenAction_weight (g : HexEvenAutomorphisms) (v : hexacode) :
    hammingNorm (evenAction g v).val = hammingNorm v.val :=
  Monomial.act_weight g.val.val v.val

private theorem nonzero_weight (v : hexacode) (hv : v ≠ 0) :
    hammingNorm v.val = 4 ∨ hammingNorm v.val = 6 := by
  rcases hex_weights v with hz | h | h
  · exact (hv (Subtype.ext (hammingNorm_eq_zero.mp hz))).elim
  · exact Or.inl h
  · exact Or.inr h

private theorem exists_word_weight (n : ℕ) (hn : n = 4 ∨ n = 6) :
    ∃ v : hexacode, hammingNorm v.val = n := by
  classical
  have hc : 0 < hexWeightCount n := by
    rw [hexacode_weight_distribution]
    rcases hn with rfl | rfl <;> norm_num
  obtain ⟨v,hv⟩ := Finset.card_pos.mp hc
  exact ⟨v,(Finset.mem_filter.mp hv).2⟩

private theorem weighted_representatives :
    ∃ r s : hexacode, hammingNorm r.val = 4 ∧ hammingNorm s.val = 6 ∧
      ∀ v : hexacode, v ≠ 0 →
        (∃ g : HexEvenAutomorphisms, evenAction g r = v) ∨
        (∃ g : HexEvenAutomorphisms, evenAction g s = v) := by
  obtain ⟨r,s,hr,hs,hcover⟩ := evenAction_two_nonzero_orbits
  have hdiff : hammingNorm r.val ≠ hammingNorm s.val := by
    intro he
    have hh : ∀ v : hexacode, v ≠ 0 → hammingNorm v.val = hammingNorm r.val := by
      intro v hv
      rcases hcover v hv with ⟨g,rfl⟩ | ⟨g,rfl⟩
      · exact evenAction_weight g r
      · exact (evenAction_weight g s).trans he.symm
    obtain ⟨a,ha⟩ := exists_word_weight 4 (Or.inl rfl)
    obtain ⟨b,hb⟩ := exists_word_weight 6 (Or.inr rfl)
    have ha0 : a ≠ 0 := by intro hz; simp [hz] at ha
    have hb0 : b ≠ 0 := by intro hz; simp [hz] at hb
    have h := (hh a ha0).trans (hh b hb0).symm
    omega
  rcases nonzero_weight r hr with hr4 | hr6
  · exact ⟨r,s,hr4,(nonzero_weight s hs).resolve_left (by omega),hcover⟩
  · refine ⟨s,r,(nonzero_weight s hs).resolve_right (by omega),hr6,?_⟩
    intro v hv
    exact (hcover v hv).symm

private theorem connect_seed (r : hexacode) (g h : HexEvenAutomorphisms) :
    evenAction (h*g⁻¹) (evenAction g r) = evenAction h r := by
  rw [← Module.End.mul_apply,← map_mul,mul_assoc,inv_mul_cancel,mul_one]

/-- Every nonzero orbit is the whole set of words of its Hamming weight. -/
theorem evenAction_orbit_eq_weight (v : hexacode) (hv : v ≠ 0) :
    (Set.range fun g : HexEvenAutomorphisms => evenAction g v) =
      {w : hexacode | hammingNorm w.val = hammingNorm v.val} := by
  obtain ⟨r,s,hr,hs,hcover⟩ := weighted_representatives
  ext w
  constructor
  · rintro ⟨g,rfl⟩
    exact evenAction_weight g v
  · intro hw
    have hw0 : w ≠ 0 := by
      intro hz
      have hp := nonzero_weight v hv
      simp only [Set.mem_ofPred_eq,hz,ZeroMemClass.coe_zero,hammingNorm_zero] at hw
      omega
    rcases hcover v hv with ⟨g,rfl⟩ | ⟨g,rfl⟩ <;>
      rcases hcover w hw0 with ⟨h,rfl⟩ | ⟨h,rfl⟩
    · exact ⟨h*g⁻¹,connect_seed r g h⟩
    · have hh := evenAction_weight h s
      have hg := evenAction_weight g r
      change hammingNorm (evenAction h s).val = hammingNorm (evenAction g r).val at hw
      omega
    · have hh := evenAction_weight h r
      have hg := evenAction_weight g s
      change hammingNorm (evenAction h r).val = hammingNorm (evenAction g s).val at hw
      omega
    · exact ⟨h*g⁻¹,connect_seed s g h⟩

/-- The two literal nonzero orbits have orders 45 and 18. -/
theorem evenAction_orbit_card (v : hexacode) (hv : v ≠ 0) :
    (Set.range fun g : HexEvenAutomorphisms => evenAction g v).ncard =
      if hammingNorm v.val = 4 then 45 else 18 := by
  classical
  rw [evenAction_orbit_eq_weight v hv]
  have he : {w : hexacode | hammingNorm w.val = hammingNorm v.val} =
      ((Finset.univ.filter fun w : hexacode => hammingNorm w.val = hammingNorm v.val) :
        Set hexacode) := by ext w; simp
  rw [he,Set.ncard_coe_finset]
  change hexWeightCount (hammingNorm v.val) = _
  rw [hexacode_weight_distribution]
  rcases nonzero_weight v hv with h | h <;> simp [h]

/-- The even nonzero orbit consists exactly of the full-weight words. -/
theorem evenAction_full_weight_of_even_orbit (v : hexacode) (hv : v ≠ 0)
    (heven : 2 ∣ (Set.range fun g : HexEvenAutomorphisms => evenAction g v).ncard) :
    hammingNorm v.val = 6 := by
  rw [evenAction_orbit_card v hv] at heven
  rcases nonzero_weight v hv with h | h
  · norm_num [h] at heven
  · exact h

/-- The actual field line through an even-orbit vector is a full-weight
binary scalar plane. -/
theorem evenAction_full_weight_point_of_even_orbit (v : hexacode) (hv : v ≠ 0)
    (heven : 2 ∣ (Set.range fun g : HexEvenAutomorphisms => evenAction g v).ncard) :
    IsFullWeightScalarPlane ((Submodule.span F {v}).restrictScalars Bit) := by
  have hweight := evenAction_full_weight_of_even_orbit v hv heven
  rcases fieldPoint_full_or_pair (Submodule.span F {v}) (finrank_span_singleton hv) with h | ⟨s,hs⟩
  · exact h
  · have hmem : v ∈ (Submodule.span F {v}).restrictScalars Bit :=
      Submodule.mem_span_singleton_self v
    rw [hs] at hmem
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < s.val.card by rw [s.property]; decide)
    exact ((full_weight_coordinate_ne_zero v.val hweight (hexPos i)) (hmem i hi)).elim

end Representation.Hexacode
