module
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Coverage
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity.Structure
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.GroupTheory.PrimeRankZero
public import Theory.Quasithin.CoprimeRank

/-!
# Three-rank of perfect subgroups in Ree two-local normalizers

Normalizer coverage puts a perfect subgroup in a full parabolic. The Suzuki
parabolic is prime to three. In the linear parabolic, perfectness kills the
field-torus coordinate, leaving a homomorphism to SL₂ with two-group kernel.
Its three-rank is therefore at most one. The ordinary unitary pushing-up
configuration uses this with its literal component quotient and radical.

Source: GLS3 Theorem 3.1.3 and §§2.3,2.6; Aschbacher–Smith C.3.5, p.150.
-/

public section
open Subgroup Theory.GroupTheory
namespace ReeF4.ConverseParabolics

theorem perfect_two_normalizer_threeRank_le_one
    {m : ℕ} (hm : 1 ≤ m) (A P : Subgroup (ReeF4.Model m))
    [Group.IsPerfect A] (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (hN : A ≤ normalizer (P : Set _)) : primeRank 3 A ≤ 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨g,s,hg⟩ := ReeF4.ConverseParabolics.normalizer_cover hm P hne hp
  let j := (MulAut.conj g).toMonoidHom.comp A.subtype
  have hj : Function.Injective j := (MulAut.conj g).injective.comp A.subtype_injective
  have hr : j.range ≤ ReeF4.ConverseParabolics.parabolic m s := by
    refine le_trans ?_ hg
    rintro _ ⟨x,rfl⟩
    exact mem_map_of_mem _ (hN x.property)
  let k := j.codRestrict _ (fun x => hr ⟨x,rfl⟩)
  have hk : Function.Injective k := fun x y he => hj (congrArg Subtype.val he)
  cases s with
  | suzuki =>
    have hb := Theory.GroupTheory.primeRank_le_of_injective 3 k hk
    have hz : primeRank 3 (ReeF4.ConverseParabolics.parabolic m .suzuki) = 0 :=
      PrimeRank.eq_zero_iff_not_dvd_card.mpr
        (ReeF4.ConverseParabolics.suzuki_parabolic_three_free hm)
    omega
  | linear =>
    let q := ReeF4.ConverseParabolics.linearProjection hm
    let f := (MonoidHom.fst _ _).comp (q.comp k)
    let t := (MonoidHom.snd _ _).comp (q.comp k)
    let : Group.IsPerfect t.range := Group.IsPerfect.range t
    have ht (x : A) : t x = 1 := congrArg Subtype.val
      (show t.rangeRestrict x = 1 from Subsingleton.elim _ _)
    have hker : IsPGroup 2 f.ker := by
      let z : f.ker →* q.ker := (k.comp f.ker.subtype).codRestrict q.ker (fun x => by
        exact Prod.ext x.property (ht x))
      exact (ReeF4.ConverseParabolics.linearProjection_ker_isPGroup hm).of_injective
        z (fun x y hh => Subtype.ext (hk (congrArg Subtype.val hh)))
    obtain ⟨n,hn⟩ := hker.exists_card_eq
    have hb := primeRank_le_of_coprime_ker 3 f (by
      rw [hn]
      exact (by decide : Nat.Coprime 3 2).pow_right n)
    exact hb.trans (Matrix.SL2.binary_odd_primeRank_le_one (by decide : Odd 3))

end ReeF4.ConverseParabolics
