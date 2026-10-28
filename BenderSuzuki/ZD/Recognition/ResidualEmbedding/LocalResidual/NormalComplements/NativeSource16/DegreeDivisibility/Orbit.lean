module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Source.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The normalizer orbit of the marked exterior involution

Put Q=T° and R=Q⟨u⟩. The inclusions Q≤R≤T give R°=Q, so invariance of
the distinguished set forces N(R) to normalize Q. Thus u's orbit lies in
the nonidentity coset Qu. One normalizer mover u↦uz, followed by the
centralizer's transitive action on Q#, covers that whole coset. Counting
the literal orbit gives |N(R):C_N(R)(u)|=|Q|.

Source: GLS4, Chapter 2, Lemma 16.4(c). The mover and model action are
separate earlier-source inputs; neither the orbit nor its order is assumed.
-/

noncomputable section
namespace BenderSuzuki.ZD.Source16DegreeDivisibility
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- A generic exterior-involution orbit is the literal nonidentity coset. -/
public theorem normalizer_orbit_eq_coset (Q : Subgroup G) (u z : G)
    (huQ : u ∉ Q) (hu2 : u ^ 2 = 1) (huC : u ∈ centralizer (Q : Set G))
    (_hz : z ∈ Q) (_hz1 : z ≠ 1)
    (hN : normalizer ((Q ⊔ zpowers u : Subgroup G) : Set G) ≤ normalizer (Q : Set G))
    (hmove : ∃ g ∈ normalizer ((Q ⊔ zpowers u : Subgroup G) : Set G),
      MulAut.conj g u = u * z)
    (htrans : ∀ x ∈ Q, x ≠ 1 →
      ∃ a ∈ normalizer (Q : Set G) ⊓ centralizer ({u} : Set G), MulAut.conj a z = x) :
    (Set.range fun g : normalizer ((Q ⊔ zpowers u : Subgroup G) : Set G) =>
      MulAut.conj (g : G) u) = Set.range (fun q : Q => (q : G) * u) := by
  classical
  let R := Q ⊔ zpowers u
  let N := normalizer (R : Set G)
  have huN : u ∈ normalizer (Q : Set G) := Subgroup.centralizer_le_normalizer _ huC
  have hu1 : u ≠ 1 := fun he => huQ (he ▸ Q.one_mem)
  have hcases (x : G) (hx : x ∈ R) : x ∈ Q ∨ ∃ q : Q, (q : G) * u = x := by
    have hp := coe_mul_of_right_le_normalizer_left Q (zpowers u) (zpowers_le.mpr huN)
    obtain ⟨a,ha,b,hb,rfl⟩ := (Set.ext_iff.mp hp x).mp hx
    change a ∈ Q at ha
    change b ∈ zpowers u at hb
    rw [mem_zpowers_iff_mem_range_orderOf,orderOf_eq_prime hu2 hu1] at hb
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hb
    have hk2 := Finset.mem_range.mp hk
    interval_cases k
    · exact Or.inl (by simpa only [pow_zero,mul_one] using ha)
    · exact Or.inr ⟨⟨a,ha⟩,by rw [pow_one]⟩
  apply Set.Subset.antisymm
  · rintro x ⟨g,rfl⟩
    have hxR : MulAut.conj (g : G) u ∈ R :=
      (mem_normalizer_iff.mp g.property u).mp (mem_sup_right (mem_zpowers u))
    rcases hcases _ hxR with hbad | hgood
    · have hh := (mem_normalizer_iff.mp (hN g.property) u).mpr hbad
      exact (huQ hh).elim
    · exact hgood
  · rintro x ⟨q,rfl⟩
    by_cases hq1 : (q : G) = 1
    · refine ⟨1,?_⟩
      simp only [OneMemClass.coe_one,MulAut.conj_apply,hq1,one_mul,inv_one,mul_one]
    obtain ⟨g,hg,hgu⟩ := hmove
    obtain ⟨a,ha,haz⟩ := htrans q q.property hq1
    have hau : MulAut.conj a u = u := by
      change a * u * a⁻¹ = u
      rw [(mem_centralizer_singleton_iff.mp ha.2),mul_inv_cancel_right]
    have haN : a ∈ N := by
      have haQ : Q.map (MulAut.conj a).toMonoidHom = Q :=
        mem_normalizer_iff_map_conj_eq.mp ha.1
      apply mem_normalizer_iff_map_conj_eq.mpr
      change (Q ⊔ zpowers u).map (MulAut.conj a).toMonoidHom = Q ⊔ zpowers u
      rw [Subgroup.map_sup,haQ,MonoidHom.map_zpowers]
      change Q ⊔ zpowers (MulAut.conj a u) = Q ⊔ zpowers u
      rw [hau]
    refine ⟨⟨a * g,N.mul_mem haN hg⟩,?_⟩
    calc
      MulAut.conj (a * g) u = MulAut.conj a (MulAut.conj g u) := by
        simp only [MulAut.conj_apply,mul_inv_rev,mul_assoc]
      _ = u * (q : G) := by rw [hgu,map_mul,hau,haz]
      _ = (q : G) * u := (mem_centralizer_iff.mp huC q q.property).symm

omit [Finite G] in
/-- Orbit-stabilizer for the literal conjugation orbit under a subgroup. -/
public theorem conjugation_orbit_card_eq_relIndex (N : Subgroup G) (u : G) :
    Nat.card (Set.range fun g : N => MulAut.conj (g : G) u) =
      (centralizer ({u} : Set G)).relIndex N := by
  let : MulAction N G := MulAction.compHom G (MulAut.conj.comp N.subtype)
  have hs : MulAction.stabilizer N u = (centralizer ({u} : Set G)).subgroupOf N := by
    ext g
    change MulAut.conj (g : G) u = u ↔ (g : G) ∈ centralizer ({u} : Set G)
    rw [MulAut.conj_apply,mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff]
  change Nat.card (MulAction.orbit N u) = _
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer N u),hs]
  rfl

variable {Z : Set G} {M : Subgroup G}

omit [Finite G] in
/-- The distinguished circle is unchanged on adjoining u inside T. -/
public theorem circle_join_involution (T : Subgroup G) {u : G} (huT : u ∈ T) :
    localCircleIn Z (localCircleIn Z T ⊔ zpowers u) = localCircleIn Z T := by
  have hRT : localCircleIn Z T ⊔ zpowers u ≤ T :=
    sup_le (localCircleIn_le Z T) (zpowers_le.mpr huT)
  rw [localCircleIn_eq_closure Z (localCircleIn Z T ⊔ zpowers u)]
  apply le_antisymm
  · calc
      _ ≤ closure (Z ∩ (T : Set G)) := closure_mono (fun _ hx => ⟨hx.1,hRT hx.2⟩)
      _ = localCircleIn Z T := (localCircleIn_eq_closure Z T).symm
  · nth_rw 1 [localCircleIn_eq_closure Z T]
    apply (closure_le _).mpr
    intro x hx
    exact subset_closure ⟨hx.1,mem_sup_left (by
      rw [localCircleIn_eq_closure]
      exact subset_closure hx)⟩

/-- Z-invariance makes the original root characteristic in this normalizer. -/
public theorem normalizer_join_le_root_normalizer (h : IsProductDisconnected Z M)
    (T : Subgroup G) {u : G} (huT : u ∈ T) :
    normalizer ((localCircleIn Z T ⊔ zpowers u : Subgroup G) : Set G) ≤
      normalizer (localCircleIn Z T : Set G) := by
  let R := localCircleIn Z T ⊔ zpowers u
  have hcircle : localCircleIn Z R = localCircleIn Z T := circle_join_involution T huT
  intro g hg
  rw [← hcircle,localCircleIn_eq_closure]
  apply mem_normalizer_fintype
  have hc : closure (Z ∩ (R : Set G)) ≤
      (closure (Z ∩ (R : Set G))).comap (MulAut.conj g).toMonoidHom := by
    apply (closure_le _).mpr
    intro x hx
    exact subset_closure ⟨h.invariant g x hx.1,(mem_normalizer_iff.mp hg x).mp hx.2⟩
  exact fun x hx => hc hx

/-- The exact source normalizer orbit and centralizer index in 16.4(c). -/
public theorem source_normalizer_orbit_card (h : IsProductDisconnected Z M)
    (T : Subgroup G) {u z : G} (huT : u ∈ T)
    (huQ : u ∉ localCircleIn Z T) (hu2 : u ^ 2 = 1)
    (huC : u ∈ centralizer (localCircleIn Z T : Set G))
    (hz : z ∈ localCircleIn Z T) (hz1 : z ≠ 1)
    (hmove : ∃ g ∈ normalizer ((localCircleIn Z T ⊔ zpowers u : Subgroup G) : Set G),
      MulAut.conj g u = u * z)
    (htrans : ∀ x ∈ localCircleIn Z T, x ≠ 1 →
      ∃ a ∈ normalizer (localCircleIn Z T : Set G) ⊓ centralizer ({u} : Set G),
        MulAut.conj a z = x) :
    Nat.card (Set.range fun g : normalizer ((localCircleIn Z T ⊔ zpowers u : Subgroup G) : Set G) =>
      MulAut.conj (g : G) u) = Nat.card (localCircleIn Z T) ∧
    (centralizer ({u} : Set G)).relIndex
      (normalizer ((localCircleIn Z T ⊔ zpowers u : Subgroup G) : Set G)) =
        Nat.card (localCircleIn Z T) := by
  have he := normalizer_orbit_eq_coset (localCircleIn Z T) u z huQ hu2 huC hz hz1
    (normalizer_join_le_root_normalizer h T huT) hmove htrans
  have hc : Nat.card (Set.range fun g : normalizer ((localCircleIn Z T ⊔ zpowers u : Subgroup G) : Set G) =>
      MulAut.conj (g : G) u) = Nat.card (localCircleIn Z T) := by
    rw [he]
    exact Nat.card_range_of_injective (fun a b he => Subtype.ext (mul_right_cancel he))
  exact ⟨hc,(conjugation_orbit_card_eq_relIndex _ u).symm.trans hc⟩

end BenderSuzuki.ZD.Source16DegreeDivisibility
