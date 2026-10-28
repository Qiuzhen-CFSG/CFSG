module
public import Theory.SpecificGroups.PSL2.QuadraticSplitTorus
public import Theory.GroupTheory.NormalAbelianTorusActions
public import Theory.GroupTheory.MarkedInternalProduct
public import Mathlib.Algebra.CharP.CharAndCard
/-!
# The quotient-action step in the original odd Hall torus product

Let B=D Dˣ be the actual Hall product from 2.4.8(5). Both factors are normal
in B and individually abelian. The image of D in the binary linear quotient
is the specified Borel complement. Its faithful embedding and the actual
quotient action transfer the quadratic displacement identity from Dˣ.
Binary split-torus rigidity therefore makes B abelian and identifies B with
the direct product of D and the kernel of that same quotient action.

The Hall, Frattini, and quotient-map producers supply only the literal
normalizations, complement, and action identities below. No quadratic-action,
inner-action, or joint-abelianness premise remains in the consumer.
Source: Aschbacher--Smith 2.4.8(5), printed pp.529--530.
-/
public section
open Subgroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter2.Section04
variable {G K F : Type*} [Group G] [Group K] [Finite K] [Field F] [Finite F]

/-- The original action on L/U turns the two normal abelian Hall factors
into the direct product of D and the actual quotient-action kernel. -/
theorem abelian_torus_product_of_linear_quotient
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) (e : K ≃* SL(2,F))
    (B D E : Subgroup G) (hB : D ⊔ E = B)
    (hDB : D ≤ B) (hEB : E ≤ B)
    (hBD : B ≤ normalizer (D : Set G)) (hBE : B ≤ normalizer (E : Set G))
    [IsMulCommutative D] [IsMulCommutative E]
    (ι : D →* K) (hi : Function.Injective ι) (ρ : B →* MulAut K)
    (hcompat : ∀ (b : B) (d : D),
      ρ b (ι d) = ι (D.normalizerMonoidHom ⟨b, hBD b.property⟩ d))
    (hinner : ∀ d : D, ρ ⟨d, hDB d.property⟩ = MulAut.conj (ι d))
    (P : Sylow 2 K) (hPN : ι.range ≤ normalizer (P : Set K))
    (hdis : Disjoint (P : Subgroup K) ι.range)
    (hgen : (P : Subgroup K) ⊔ ι.range = normalizer (P : Set K))
    (hroot : ∀ b : B, (b : G) ∈ E → (P : Subgroup K).map (ρ b).toMonoidHom = P) :
    IsMulCommutative B ∧ B = D ⊔ ρ.ker.map B.subtype ∧
      Disjoint D (ρ.ker.map B.subtype) ∧
      (B : Set G) = (D : Set G) * (ρ.ker.map B.subtype : Set G) ∧
      Nonempty (B ≃* D × (ρ.ker.map B.subtype)) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let eP := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F))
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    have hh : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (show 2 ≤ n by omega)
    omega
  have hK : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro k hk
    have hz : eP k ∈ center PSL(2,F) := (centerCongr eP ⟨k, hk⟩).property
    have he : eP k = 1 := by
      simpa only [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot, mem_bot] using hz
    exact mem_bot.mpr (eP.injective (he.trans (map_one eP).symm))
  obtain ⟨hab, hsplit, hd, hprod⟩ :=
    Theory.GroupTheory.NormalAbelianTorus.abelian_and_kernel_product B D E hB hDB hEB
      hBD hBE ι hi hK ρ hcompat hinner (fun b hb hmap hquad =>
        Theory.PSL2.QuadraticTorus.fixes_and_inner_of_equiv eP hlarge
          P ι.range hPN hdis hgen (ρ b) (hroot b hb) hmap hquad)
  have hcomm : D ≤ centralizer (ρ.ker.map B.subtype : Set G) := by
    let := hab
    intro d hd c hc
    have hcB : c ∈ B := (map_subtype_le ρ.ker) hc
    exact congrArg Subtype.val (mul_comm' (⟨c, hcB⟩ : B) ⟨d, hDB hd⟩)
  obtain ⟨f, _, _⟩ := Theory.GroupTheory.exists_marked_internalProductEquiv
    B D (ρ.ker.map B.subtype) hsplit.symm hd hcomm
  exact ⟨hab, hsplit, hd, hprod, ⟨f⟩⟩

/-- Literal D and Dˣ specialization of the quotient-action conclusion in
2.4.8(5). Individual commutativity of D supplies it for its actual conjugate. -/
theorem conjugate_torus_abelian_of_linear_quotient
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) (e : K ≃* SL(2,F))
    (B D : Subgroup G) (x : G)
    (hB : D ⊔ D.map (MulAut.conj x⁻¹).toMonoidHom = B)
    (hDB : D ≤ B) (hEB : D.map (MulAut.conj x⁻¹).toMonoidHom ≤ B)
    (hBD : B ≤ normalizer (D : Set G))
    (hBE : B ≤ normalizer (D.map (MulAut.conj x⁻¹).toMonoidHom : Set G))
    [IsMulCommutative D]
    (ι : D →* K) (hi : Function.Injective ι) (ρ : B →* MulAut K)
    (hcompat : ∀ (b : B) (d : D),
      ρ b (ι d) = ι (D.normalizerMonoidHom ⟨b, hBD b.property⟩ d))
    (hinner : ∀ d : D, ρ ⟨d, hDB d.property⟩ = MulAut.conj (ι d))
    (P : Sylow 2 K) (hPN : ι.range ≤ normalizer (P : Set K))
    (hdis : Disjoint (P : Subgroup K) ι.range)
    (hgen : (P : Subgroup K) ⊔ ι.range = normalizer (P : Set K))
    (hroot : ∀ b : B, (b : G) ∈ D.map (MulAut.conj x⁻¹).toMonoidHom →
      (P : Subgroup K).map (ρ b).toMonoidHom = P) :
    IsMulCommutative B ∧ B = D ⊔ ρ.ker.map B.subtype ∧
      Disjoint D (ρ.ker.map B.subtype) ∧
      (B : Set G) = (D : Set G) * (ρ.ker.map B.subtype : Set G) ∧
      Nonempty (B ≃* D × (ρ.ker.map B.subtype)) := by
  let E := D.map (MulAut.conj x⁻¹).toMonoidHom
  let f : D ≃* E := (MulAut.conj x⁻¹).subgroupMap D
  let : IsMulCommutative E := ⟨⟨fun a b => f.symm.injective (by
    rw [map_mul, map_mul, mul_comm'])⟩⟩
  exact abelian_torus_product_of_linear_quotient hn hF e B D E hB hDB hEB hBD hBE
    ι hi ρ hcompat hinner P hPN hdis hgen hroot

end CFSG.Quasithin.Chapter2.Section04
