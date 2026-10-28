module
public import Theory.Representation.AlternatingFiveInnerDisplacement
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.Representation.NormalElementaryQuotient.OriginalAction

/-!
# A₅ components and rank-one actors on a reduced module

For a normal K with K/O₂(K) isomorphic to A₅, a noncentral reduced binary
module detects that whole quotient. Compare a second action whose restriction
to K has kernel O₂(K). An actor whose second image lies in K and has square
one induces the same inner automorphism in both actions. If its displacement
on the reduced module is at most one, the A₅ quintic-commutator bound makes
its second image trivial. All quotient maps and relative kernels are retained.

Source: Aschbacher--Smith, 14.3.25, printed p.1001. This is the nonsolvable
seed argument's transvection step, with no irreducibility assumption.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {H D : Type*} [Group H] [Finite H] [Group D]

/-- A small actor lying in the second A₅ image is killed by that action. -/
theorem reduced_alternatingFive_inner_actor_trivial
    (W K : Subgroup H) [W.Normal] [K.Normal] [IsElementaryAbelian 2 W]
    (hr : IsPReduced 2 W) (hm : ¬ K ≤ centralizer (W : Set H))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (f : H →* D) (hk : (f.comp K.subtype).ker = pCore 2 K)
    (a : H) (ha : ∃ c : K, f c = f a) (ha2 : f a ^ 2 = 1)
    (hd : Module.finrank (ZMod 2)
      (NormalElementaryQuotient.originalAction W a - LinearMap.id).range ≤ 1) : f a = 1 := by
  let ρ := NormalElementaryQuotient.originalAction W
  have hcore : pCore 2 K ≤ (ρ.comp K.subtype).ker := by
    have hp : (pCore 2 K).map K.subtype ≤ pCore 2 H :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map K.subtype⟩
    intro k hkk
    change ρ (k:H) = 1
    apply (show ρ.ker = centralizer (W : Set H) from NormalElementaryQuotient.originalAction_kernel W).ge
    exact le_centralizer_iff.mp hr.le_centralizer_pCore (hp (mem_map_of_mem K.subtype hkk))
  let q := QuotientGroup.mk' (pCore 2 K)
  let β := QuotientGroup.lift (pCore 2 K) (ρ.comp K.subtype) hcore
  let σ : Representation (ZMod 2) (alternatingGroup (Fin 5)) (Additive W) := β.comp e.symm.toMonoidHom
  have heval (k : K) : σ (e (q k)) = ρ (k:H) := by
    change β (e.symm (e (q k))) = _
    rw [e.symm_apply_apply]
    rfl
  have hinj : Function.Injective σ := by
    rcases (MonoidHom.normal_ker σ).eq_bot_or_eq_top with hb | ht
    · exact σ.ker_eq_bot_iff.mp hb
    · exfalso
      apply hm
      intro k hkk
      have he : σ (e (q ⟨k,hkk⟩)) = 1 := ht.ge (mem_top _)
      rw [heval] at he
      exact (NormalElementaryQuotient.originalAction_kernel W).le he
  have hquot {k l : K} (hh : f k = f l) : q k = q l := by
    apply QuotientGroup.eq.mpr
    rw [← hk]
    change f ((k:H)⁻¹ * (l:H)) = 1
    rw [map_mul,map_inv,hh,inv_mul_cancel]
  obtain ⟨c,hc⟩ := ha
  let s := e (q c)
  have hs : s ^ 2 = 1 := by
    change e (q c) ^ 2 = 1
    rw [← map_pow, ← map_pow]
    have hh : q (c^2) = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [← hk]
      change f ((c:H)^2) = 1
      rw [map_pow,hc,ha2]
    rw [hh,map_one]
  have hinter : ∀ b, ρ.asGroupHom a * σ.asGroupHom b * (ρ.asGroupHom a)⁻¹ =
      σ.asGroupHom (s*b*s⁻¹) := by
    intro b
    obtain ⟨b',rfl⟩ := e.surjective b
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) b'
    let k' : K := ⟨a*(k:H)*a⁻¹, (inferInstance : K.Normal).conj_mem _ k.property a⟩
    have hf : f (k':H) = f ((c*k*c⁻¹ : K):H) := by
      change f (a*(k:H)*a⁻¹) = f ((c:H)*(k:H)*(c:H)⁻¹)
      simp only [map_mul,map_inv,hc]
    have hq : q k' = q (c*k*c⁻¹) := hquot hf
    apply Units.ext
    change ρ a * σ (e (q k)) * ρ a⁻¹ = σ (s*e (q k)*s⁻¹)
    rw [heval, ← map_mul, ← map_mul]
    change ρ (k':H) = _
    rw [← heval k', hq]
    simp only [map_mul,map_inv,s]
  have hs1 := AlternatingFiveInvolutionDisplacement.inner_involution_eq_one_of_rank_le_one
    σ hinj (ρ.asGroupHom a) s hs hinter hd
  have hqc : q c = 1 := e.injective (hs1.trans e.map_one.symm)
  have hcK : c ∈ (f.comp K.subtype).ker := hk ▸ (QuotientGroup.eq_one_iff _).mp hqc
  exact hc.symm.trans hcK
end Theory.GroupTheory
