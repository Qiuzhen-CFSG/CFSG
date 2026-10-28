module
public import Theory.SpecificGroups.PGL2.PerfectCentralizer
public import Theory.SpecificGroups.PSL2.PrimeAutomorphismCentralizer
public import Theory.GroupTheory.SolvableOuterQuotient
/-!
# A perfect subgroup determines the centralizer of a normal prime PSL₂ model

The actual full automorphism group is PGL₂. A nontrivial perfect subgroup
therefore has trivial centralizer in that automorphism group. Conjugation
on a normal PSL₂ component identifies its ambient centralizer with the
centralizer of any nontrivial perfect subgroup contained in it. The
conjugation kernel remains the actual component centralizer.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Matrix Subgroup
open scoped MatrixGroups IsMulCommutative
namespace Theory.PSL2
open GorensteinWalter

theorem prime_field_automorphism_centralizer_eq_bot_of_perfect
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    {F : Type} [Field F] [Finite F] (hcard : Nat.card F = p)
    {Q : Type*} [Group Q] (eQ : Q ≃* PSL(2, F))
    (D : Subgroup (MulAut Q)) [Group.IsPerfect D] (hne : D ≠ ⊥) :
    centralizer (D : Set (MulAut Q)) = ⊥ := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  let hF : IsOddPrimePower (Nat.card (F)) :=
    ⟨p,1,Fact.out,hodd,by decide,by simpa using hcard⟩
  let hc : 3 < Nat.card (F) := by simpa only [hcard] using hp
  let eA : PGL2 (F) ≃* MulAut PSL(2,F) :=
    MulEquiv.ofBijective (pgl2InnerAutPSL2 (F) hF hc)
      ⟨pgl2InnerAutPSL2_injective (F) hF hc,
        prime_card_pgl_coverage (p := p) (F) hcard hF hc⟩
  let e := (MulAut.congr eQ).trans eA.symm
  let E := D.map e.toMonoidHom
  let : Group.IsPerfect E := Group.IsPerfect.map _
  have hE : E ≠ ⊥ := fun h => hne ((map_eq_bot_iff_of_injective D e.injective).mp h)
  have hz := Theory.PGL2.centralizer_eq_bot_of_perfect E hE
  apply bot_unique
  intro a ha
  have hca : e a ∈ centralizer (E : Set _) := by
    rintro _ ⟨d,hd,rfl⟩
    exact (map_mul e d a).symm.trans ((congrArg e (ha d hd)).trans (map_mul e a d))
  rw [hz,mem_bot] at hca
  exact mem_bot.mpr (e.injective (hca.trans (map_one e).symm))
end Theory.PSL2
namespace Theory.PSL2
open GorensteinWalter

theorem centralizer_eq_of_perfect_in_prime_component
    {H : Type*} [Group H] (D L : Subgroup H) [D.Normal] [Group.IsPerfect L]
    (hL : L ≠ ⊥) (hLD : L ≤ D)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    {F : Type} [Field F] [Finite F] (hcard : Nat.card F = p)
    (eD : D ≃* PSL(2,F)) :
    centralizer (L : Set H) = centralizer (D : Set H) := by
  let φ : H →* MulAut D := MulAut.conjNormal
  have hz : center D = ⊥ := by
    apply bot_unique
    intro d hd
    apply mem_bot.mpr
    apply eD.injective
    rw [map_one]
    apply mem_bot.mp
    rw [← psl2_center_eq_bot F]
    rw [mem_center_iff]
    intro y
    obtain ⟨x,rfl⟩ := eD.surjective y
    simpa only [← map_mul] using congrArg eD ((mem_center_iff.mp hd) x)
  have hi : Function.Injective (MulAut.conj : D →* MulAut D) :=
    Theory.GroupTheory.conj_injective_of_center_eq_bot hz
  let E := L.map φ
  let : Group.IsPerfect E := Group.IsPerfect.map _
  have hE : E ≠ ⊥ := by
    intro he
    obtain ⟨l,hl,hl1⟩ := L.bot_or_exists_ne_one.resolve_left hL
    have hlφ : φ l = 1 := mem_bot.mp (he ▸ mem_map_of_mem φ hl)
    have heq : MulAut.conj (⟨l,hLD hl⟩ : D) = φ l := by
      ext d
      rfl
    have ht : (⟨l,hLD hl⟩ : D) = 1 := hi (by rw [map_one,heq]; exact hlφ)
    exact hl1 (congrArg D.subtype ht)
  have hc := prime_field_automorphism_centralizer_eq_bot_of_perfect hp hcard eD E hE
  apply le_antisymm _ (centralizer_le hLD)
  intro a ha
  have hφ : φ a ∈ centralizer (E : Set _) := by
    rintro _ ⟨l,hl,rfl⟩
    exact (map_mul φ l a).symm.trans ((congrArg φ (ha l hl)).trans (map_mul φ a l))
  rw [hc,mem_bot] at hφ
  rw [← MulAut.conjNormal_ker_eq_centralizer D]
  exact hφ
end Theory.PSL2
