module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.Shearing

/-!
# Support of the two Thompson fibers in Lemma 12.8

The half-order involution of a mixed pair is distinguished when the rotation
order is divisible by four; the distinguished involution-product equality
proves this without any ambient class-exhaustion hypothesis. In the other
case the dihedral exchange identity and shearing put it in the actor class.
Fusion control excludes the first case when the actor centralizes the
distinguished subgroup. This gives the two-term Thompson order formula and
the vanishing of its distinguished term in the centralizing case.

Source: GLS4, Chapter 2, proof of Lemma 12.8, using 12.2(c,e) and 12.7,
`refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1 TwoInvolutionClassOrder
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
namespace ResidualNumerics

omit [Finite G] in
private theorem mem_Z_of_isConj (h : IsProductDisconnected Z M)
    {a b : G} (ha : a ∈ Z) (hab : IsConj a b) : b ∈ Z := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  exact hg ▸ h.invariant g a ha

omit [Finite G] in
private theorem conj_mem_A (h : IsProductDisconnected Z M)
    {m a : G} (hm : m ∈ M) (ha : a ∈ closure (Z ∩ (M : Set G))) :
    MulAut.conj m a ∈ closure (Z ∩ (M : Set G)) := by
  have hmN : m ∈ normalizer (closure (Z ∩ (M : Set G)) : Set G) := by
    rwa [distinguishedClosure_normalizer h]
  exact (mem_normalizer_iff.mp hmN a).mp ha

private theorem conjugate_centralizes_A
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {u v : G} (hu : PFAppendixIII.IsInvolution u) (huM : u ∈ M)
    (huA : u ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G))
    (hv : IsConj u v) (hvM : v ∈ M) :
    v ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G) := by
  have hvI : PFAppendixIII.IsInvolution v := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp hv
    exact IsInvolution.map_of_injective hu (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  obtain ⟨S, hSM, hf⟩ := r.fusion
  obtain ⟨m, hm⟩ := involution_fusion_in_subgroup S hSM hf hu hvI huM hvM hv
  intro a ha
  have haA : (m : G)⁻¹ * a * m ∈ closure (Z ∩ (M : Set G)) := by
    simpa only [MulAut.conj_apply, inv_inv] using conj_mem_A h (M.inv_mem m.property) ha
  have hh := congrArg (MulAut.conj (m : G)) (mem_centralizer_iff.mp huA _ haA)
  have hmu : MulAut.conj (m : G) u = v := hm
  have hma : MulAut.conj (m : G) ((m : G)⁻¹ * a * m) = a := by
    simp [MulAut.conj_apply, mul_assoc]
  simpa only [map_mul, hmu, hma] using hh


private theorem support
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (htM : t ∉ M)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hP : {v : G | PFAppendixIII.IsInvolution v ∧ ∃ x ∈ Z, ∃ y ∈ Z, v = x * y} = Z)
    (hs : ∀ v s : G, IsConj u v → s ∈ Z → Commute v s → IsConj u (v * s)) :
    ∀ a b : G, IsConj z a → IsConj u b →
      (IsConj z (halfOrder a b) ∧
        u ∉ centralizer (closure (Z ∩ (M : Set G)) : Set G)) ∨
      IsConj u (halfOrder a b) := by
  have huZ := not_mem_Z_of_mem_residualPairStabilizer h htM huD
  have hzI := h.involutions z hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime hzI.sq_eq_one hzI.ne_one
  have hfixed {v : G} (hv : IsConj u v) :
      (IsConj z (halfOrder z v) ∧
        u ∉ centralizer (closure (Z ∩ (M : Set G)) : Set G)) ∨
      IsConj u (halfOrder z v) := by
    have hvZ : v ∉ Z := fun hvZ => huZ (mem_Z_of_isConj h hvZ hv.symm)
    have hvI : PFAppendixIII.IsInvolution v := by
      obtain ⟨g, rfl⟩ := isConj_iff.mp hv
      exact IsInvolution.map_of_injective hu (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    have hv2 : orderOf v = 2 := orderOf_eq_prime hvI.sq_eq_one hvI.ne_one
    have hnv : ¬ IsConj z v := fun hh => hvZ (mem_Z_of_isConj h hz hh)
    have hw := halfOrder_properties hz2 hv2 hnv (IsConj.refl z) (IsConj.refl v)
    have heven : Even (orderOf (z * v)) := by
      apply Nat.not_odd_iff_even.mp
      exact fun ho => hnv (isConj_of_involutions_odd_product z v hzI.sq_eq_one hvI.sq_eq_one ho)
    by_cases hdiv : orderOf (z * v) % 4 = 0
    · have hzwZ := mem_Z_of_isConj h hz
        (DihedralHalfOrderClasses.preserve hz2 hv2 hdiv).1
      have hwZ : halfOrder z v ∈ Z := by
        rw [← hP]
        refine ⟨(orderOf_eq_prime_iff.mp hw.1).symm, z, hz, z * halfOrder z v, hzwZ, ?_⟩
        rw [← mul_assoc, ← pow_two, hzI.sq_eq_one, one_mul]
      refine Or.inl ⟨r.one_class z hz _ hwZ, ?_⟩
      intro huA
      have hwM : halfOrder z v ∈ M := mem_of_commute h hz hzM hw.2.1.symm
      have hvM := mem_of_commute h hwZ hwM hw.2.2
      have hvc := conjugate_centralizes_A h r hu huD.1 huA hv hvM
      have hcz : Commute z v := mem_centralizer_iff.mp hvc z (subset_closure ⟨hz, hzM⟩)
      have hp : (z * v) ^ 2 = 1 := by rw [hcz.mul_pow, hzI.sq_eq_one, hvI.sq_eq_one, one_mul]
      have hd := orderOf_dvd_of_pow_eq_one hp
      have hl := Nat.le_of_dvd (by decide : 0 < 2) hd
      have hpos := orderOf_pos (z * v)
      omega
    · have hmod : orderOf (z * v) % 4 = 2 := by
        obtain ⟨k, hk⟩ := heven
        omega
      have hvwZ := mem_Z_of_isConj h hz
        (DihedralHalfOrderClasses.exchange hz2 hv2 hmod).2
      have hc : Commute v (v * halfOrder z v) := (Commute.refl v).mul_right hw.2.2.symm
      have hh := hs v (v * halfOrder z v) hv hvwZ hc
      exact Or.inr (by simpa only [← mul_assoc, ← pow_two, hvI.sq_eq_one, one_mul] using hh)
  intro a b ha hb
  obtain ⟨g, hg⟩ := isConj_iff.mp ha.symm
  have hgb : IsConj u (MulAut.conj g b) := hb.trans (isConj_iff.mpr ⟨g, rfl⟩)
  have he : halfOrder z (MulAut.conj g b) = MulAut.conj g (halfOrder a b) := by
    rw [← hg]
    exact halfOrder_map (MulAut.conj g) a b
  rcases hfixed hgb with ⟨hh, hn⟩ | hh
  · rw [he] at hh
    exact Or.inl ⟨hh.trans (isConj_iff.mpr ⟨g, rfl⟩).symm, hn⟩
  · rw [he] at hh
    exact Or.inr (hh.trans (isConj_iff.mpr ⟨g, rfl⟩).symm)

end ResidualNumerics

/-- Mixed half-order powers are supported on the distinguished and actor
classes. The distinguished class can occur only for a noncentral actor. -/
public theorem proper_residualGenerated_mixed_support
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t v : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    ∀ a b : G, IsConj z a → IsConj v b →
      (IsConj z (halfOrder a b) ∧
        v ∉ centralizer (closure (Z ∩ (M : Set G)) : Set G)) ∨
      IsConj v (halfOrder a b) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hP, _⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  exact ResidualNumerics.support h.disconnected r hz hzM htM hvD hv hP
    (fun a b hab hb hc => proper_residualGenerated_commuting_mixed_fusion_of_local
      h r ha hz hzM ht htM hL heven hlocal hvD hv hab hb hc)

/-- The distinguished Thompson fiber is empty when the actor centralizes A.
No statement about the number of ambient involution classes is needed. -/
public theorem proper_residualGenerated_central_kappa_zero
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t v : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v)
    (hc : v ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G)) :
    kappa z v z = 0 := by
  have hs := proper_residualGenerated_mixed_support h r ha hz hzM ht htM hL heven hlocal hvD hv
  have : IsEmpty (Fiber z v z) := ⟨fun p => by
    rcases hs _ _ p.property.1 p.property.2.1 with ⟨_, hn⟩ | hh
    · exact hn hc
    · rw [p.property.2.2] at hh
      exact not_mem_Z_of_mem_residualPairStabilizer h.disconnected htM hvD
        (ResidualNumerics.mem_Z_of_isConj h.disconnected hz hh.symm)⟩
  have hk : kappa z v z = Nat.card (Fiber z v z) := by
    simp only [kappa_def, Fiber, halfOrder_def]
  rw [hk]
  exact Nat.card_of_isEmpty

end BenderSuzuki.ZD
