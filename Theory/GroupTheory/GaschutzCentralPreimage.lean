module
public import Theory.GroupTheory.GaschutzElementaryPair
public import Theory.GroupTheory.CyclicHallNormalizerEscape
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Gaschütz complements modulo a commutator kernel

An elementary abelian supplement to a normal p-subgroup in a Sylow
subgroup gives a complement after quotienting by any normal subgroup
containing its commutators. The quotient image is abelian, so the proved
Gaschütz theorem applies to the image of the actual Sylow subgroup.

The inverse image of a quotient complement supplements the original normal
subgroup and intersects it exactly in the quotient kernel. Its epimorphism
onto the original quotient is the restriction of the original quotient map.
This retains the central preimage needed when the kernel is central.
Sylow conjugacy also arranges that a chosen prime subgroup lies in the
complement whenever its prime does not divide the normal factor's order.

Source application: Delgado--Goldschmidt--Stellmacher, Groups and Graphs
(1985), the first splitting step in (5.16), printed p.117.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Split the abelian image using the original elementary Sylow supplement. -/
theorem quotient_split_of_elementary_sylow_supplement
    {p : ℕ} [Fact p.Prime] (N Z : Subgroup G) [N.Normal] [Z.Normal]
    (hder : ⁅N,N⁆ ≤ Z) (hN : IsPGroup p N)
    (P : Sylow p G) (A : Subgroup G) [IsElementaryAbelian p A]
    (hgen : N ⊔ A = (P : Subgroup G)) :
    ∃ C : Subgroup (G ⧸ Z), (N.map (QuotientGroup.mk' Z)).IsComplement' C := by
  let q := QuotientGroup.mk' Z
  let V := N.map q
  let : V.Normal := QuotientGroup.map_normal Z N
  let : IsMulCommutative V := commutator_self_eq_bot_iff.mp (by
    rw [←map_commutator]
    apply le_bot_iff.mp
    apply (map_le_iff_le_comap).mpr
    simpa only [q,MonoidHom.comap_bot,QuotientGroup.ker_mk'] using hder)
  let A₀ := A.map q
  let : IsElementaryAbelian p A₀ := IsElementaryAbelian.map q
  apply exists_complement_of_sylow_elementary V (hN.map q)
    (P.mapSurjective (QuotientGroup.mk'_surjective Z)) A₀
  change N.map q ⊔ A.map q = (P : Subgroup G).map q
  rw [←Subgroup.map_sup,hgen]

omit [Finite G] in
/-- The inverse image retains both product identities and the literal quotient map. -/
theorem exists_preimage_of_quotient_complement
    (N Z : Subgroup G) [N.Normal] [Z.Normal] (hZN : Z ≤ N)
    (C : Subgroup (G ⧸ Z)) (hC : (N.map (QuotientGroup.mk' Z)).IsComplement' C) :
    ∃ H : Subgroup G, H = C.comap (QuotientGroup.mk' Z) ∧
      Z ≤ H ∧ N ⊓ H = Z ∧ N ⊔ H = ⊤ ∧
      ∃ f : H →* G ⧸ N, Function.Surjective f ∧
        f.ker = Z.subgroupOf H ∧
        ∀ x : H, f x = QuotientGroup.mk' N (x : G) := by
  let q := QuotientGroup.mk' Z
  let H := C.comap q
  have hZH : Z ≤ H := by
    intro z hz
    change q z ∈ C
    rw [show q z = 1 from (QuotientGroup.eq_one_iff _).mpr hz]
    exact C.one_mem
  have hinf : N ⊓ H = Z := by
    apply le_antisymm
    · intro x hx
      exact (QuotientGroup.eq_one_iff x).mp
        (Subgroup.disjoint_def.mp hC.disjoint (mem_map_of_mem q hx.1) hx.2)
    · exact le_inf hZN hZH
  have hsup : N ⊔ H = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨⟨n,c⟩,he⟩ := hC.2 (q x)
    obtain ⟨y,hy,hey⟩ := n.property
    have hh : y⁻¹ * x ∈ H := by
      change q (y⁻¹ * x) ∈ C
      rw [map_mul,map_inv]
      change (n : G ⧸ Z) * (c : G ⧸ Z) = q x at he
      rw [hey,←he,inv_mul_cancel_left]
      exact c.property
    simpa only [mul_inv_cancel_left] using (N ⊔ H).mul_mem
      (mem_sup_left hy) (mem_sup_right hh)
  let f : H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective N x
    have hy : y ∈ N ⊔ H := hsup ▸ mem_top y
    rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left N H le_normalizer_of_normal] at hy
    obtain ⟨n,hn,z,hz,rfl⟩ := hy
    refine ⟨⟨z,hz⟩,?_⟩
    change QuotientGroup.mk' N z = QuotientGroup.mk' N (n*z)
    rw [map_mul]
    have hnq : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [hnq,one_mul]
  refine ⟨H,rfl,hZH,hinf,hsup,f,hf,?_,fun _ => rfl⟩
  ext x
  change QuotientGroup.mk' N (x : G) = 1 ↔ (x : G) ∈ Z
  change ((x : G) : G ⧸ N) = 1 ↔ (x : G) ∈ Z
  rw [QuotientGroup.eq_one_iff]
  exact ⟨fun hx => hinf ▸ ⟨hx,x.property⟩,fun hx => hZN hx⟩
/-- Choose a conjugate complement containing a prescribed coprime prime subgroup. -/
theorem complement_containing_prime_subgroup
    {r : ℕ} [Fact r.Prime] (N C A : Subgroup G) [N.Normal]
    (hC : N.IsComplement' C) (hA : IsPGroup r A) (hr : ¬ r ∣ Nat.card N) :
    ∃ D : Subgroup G, N.IsComplement' D ∧ A ≤ D := by
  obtain ⟨g,hg⟩ := exists_conj_le_of_prime_not_dvd_index C A
    (by rwa [hC.index_eq_card]) hA
  let e := MulAut.conj g⁻¹
  refine ⟨C.map e.toMonoidHom,?_,?_⟩
  · apply isComplement'_of_card_mul_and_disjoint
    · rw [card_map_of_injective e.injective]
      exact hC.card_mul_card
    · have hh := disjoint_map (f := e.toMonoidHom) e.injective hC.disjoint
      have hn : N.map e.toMonoidHom = N := Subgroup.Normal.map_conj_eq N g⁻¹
      rwa [hn] at hh
  · intro a ha
    refine ⟨MulAut.conj g a,hg (mem_map_of_mem (MulAut.conj g).toMonoidHom ha),?_⟩
    change g⁻¹ * (g * a * g⁻¹) * (g⁻¹)⁻¹ = a
    group
end Theory.GroupTheory
