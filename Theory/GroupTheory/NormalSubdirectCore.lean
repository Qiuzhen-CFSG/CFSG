module
public import Theory.GroupTheory.PResidual.OddCoreSupplement
public import Theory.GroupTheory.PPerfectHom

/-!
# Prime cores in normal subdirect products

A normal subgroup projecting onto both factors contains every commutator
supported on a single factor. Its quotient is therefore abelian. If both
factors are p-perfect, the quotient is also p-perfect and has order prime
to p, so the whole ambient p-core lies in the subgroup.

Source application: Aschbacher–Smith, proof of 14.7.32, printed p.1058,
identifying the point residual's two-core in the paired field-four Borel.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Subgroup
variable {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]

/-- A normal subgroup projecting onto both p-perfect factors contains the ambient p-core. -/
theorem pCore_le_normal_subdirect {p : ℕ} [Fact p.Prime]
    (hA : IsPPerfect p A) (hB : IsPPerfect p B)
    (N : Subgroup (A × B)) [N.Normal]
    (hf : N.map (MonoidHom.fst A B) = ⊤)
    (hs : N.map (MonoidHom.snd A B) = ⊤) : pCore p (A × B) ≤ N := by
  have hcomm : _root_.commutator (A × B) ≤ N := by
    rw [_root_.commutator_def]
    apply commutator_le.mpr
    intro x _ y _
    obtain ⟨a,ha,hea⟩ := (show y.1 ∈ N.map (MonoidHom.fst A B) from hf ▸ mem_top _)
    obtain ⟨b,hb,heb⟩ := (show y.2 ∈ N.map (MonoidHom.snd A B) from hs ▸ mem_top _)
    have h1 : ⁅(x.1,(1:B)),a⁆ ∈ N :=
      commutator_le_right (⊤ : Subgroup (A × B)) N
        (commutator_mem_commutator (mem_top _) ha)
    have h2 : ⁅((1:A),x.2),b⁆ ∈ N :=
      commutator_le_right (⊤ : Subgroup (A × B)) N
        (commutator_mem_commutator (mem_top _) hb)
    have he : ⁅x,y⁆ = ⁅(x.1,(1:B)),a⁆ * ⁅((1:A),x.2),b⁆ := by
      apply Prod.ext <;> simp [commutatorElement_def, ←hea, ←heb]
    rw [he]
    exact N.mul_mem h1 h2
  let : IsMulCommutative ((A × B) ⧸ N) :=
    Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  let : CommGroup ((A × B) ⧸ N) := IsMulCommutative.instCommGroup
  have hp : IsPPerfect p (A × B) := by
    intro D hD hQ
    let := hD
    let q := QuotientGroup.mk' D
    have h1 := hA.hom_eq_one_of_isPGroup hQ (q.comp (MonoidHom.inl A B))
    have h2 := hB.hom_eq_one_of_isPGroup hQ (q.comp (MonoidHom.inr A B))
    apply top_unique
    rintro ⟨a,b⟩ _
    apply (QuotientGroup.eq_one_iff _).mp
    have he : (a,b) = (a,1)*(1,b) := by simp
    change q (a,b) = 1
    rw [he,map_mul]
    exact (congrArg₂ (· * ·) (DFunLike.congr_fun h1 a) (DFunLike.congr_fun h2 b)).trans
      (one_mul 1)
  let q := QuotientGroup.mk' N
  have hc := coprime_card_of_isPPerfect_commGroup
    (hp.of_surjective q (QuotientGroup.mk'_surjective N))
  intro x hx
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := p) (G := A × B)).exists_pow_pow_eq_one ⟨x,hx⟩
  have hpow : q x ^ (p^n) = 1 := by
    rw [←map_pow,show x^(p^n)=1 from congrArg Subtype.val hn,map_one]
  have hn : orderOf (q x) = 1 := Nat.eq_one_of_dvd_coprimes (hc.pow_left n)
    (orderOf_dvd_of_pow_eq_one hpow) (_root_.orderOf_dvd_natCard (q x))
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp hn)
end Subgroup
