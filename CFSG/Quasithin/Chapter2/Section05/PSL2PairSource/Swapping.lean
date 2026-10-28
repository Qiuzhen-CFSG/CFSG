module

public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.InnerCase
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# Excluding factor swapping in the marked class

For an involution swapping K and Kˣ, multiplication of k with its image
gives an injective diagonal homomorphism from K to the involution
centralizer. Its image lies in Kᵍ: conjugate the homomorphism back to C_G(t)
and use the proved equality O²(C_G(t)) = K and p-perfectness of K.
The diagonal involutions then belong both to the original z-class and
the t-class, contradicting the incoming source nonfusion hypothesis.

This avoids assuming a diagonal centralizer or a residual equality for it.
Source: Aschbacher–Smith, proof of 2.5.21, printed p.566.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.CounterexampleGeometry
namespace CFSG.Quasithin.Chapter2.PSL2PairSource.Incoming
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {p : ℕ} [Fact p.Prime]

private theorem image_le_conjugate (d : Incoming κ G p) (g : G)
    (f : d.K →* G) (hf : f.range ≤ centralizer ({g⁻¹ * d.t * g} : Set G)) :
    f.range ≤ conjugate d.K g := by
  let J := centralizer ({d.t} : Set G)
  have hmap : (centralizer ({g⁻¹ * d.t * g} : Set G)).map
      (MulAut.conj g).toMonoidHom = J := by
    rw [map_centralizer_equiv, Set.image_singleton]
    congr 2
    change g * (g⁻¹ * d.t * g) * g⁻¹ = d.t
    group
  let r : d.K →* J := ((MulAut.conj g).toMonoidHom.comp f).codRestrict J (by
    intro k
    rw [← hmap]
    exact mem_map.mpr ⟨f k, hf ⟨k, rfl⟩, rfl⟩)
  have hKp := isPPerfect_embedded_pResidual 2 J
  rw [d.twoResidual_eq] at hKp
  have hR := map_pResidual_le 2 r
  rw [(pResidual_eq_top_iff 2 d.K).mpr hKp] at hR
  rintro a ⟨k, rfl⟩
  have hrK : (r k : G) ∈ d.K := by
    exact d.twoResidual_eq.le (mem_map.mpr ⟨r k, hR (mem_map.mpr ⟨k, mem_top _, rfl⟩), rfl⟩)
  exact mem_map.mpr ⟨r k, hrK, by
    change g⁻¹ * (g * f k * g⁻¹) * (g⁻¹)⁻¹ = f k
    group⟩

/-- A conjugate of the marked involution cannot swap the two factors.
The fixed diagonal copy of K lies in the conjugate two-residual; its
involutions would consequently belong to both the t-class and z-class. -/
theorem false_of_factor_swapping (d : Incoming κ G p) (g : G)
    (hswap : d.K.map (MulAut.conj (g⁻¹ * d.t * g)).toMonoidHom = conjugate d.K d.x) :
    False := by
  let i := g⁻¹ * d.t * g
  let L := conjugate d.K d.x
  have hi2 : i ^ 2 = 1 := by
    have ht : d.t ^ 2 = 1 := by rw [← d.t_order]; exact pow_orderOf_eq_one d.t
    simpa only [map_pow, MulAut.conj_apply, inv_inv, map_one] using congrArg (MulAut.conj g⁻¹) ht
  let b : d.K →* G := (MulAut.conj i).toMonoidHom.comp d.K.subtype
  have hbL (k : d.K) : b k ∈ L := by
    change b k ∈ conjugate d.K d.x
    rw [← hswap]
    exact mem_map.mpr ⟨k, k.property, rfl⟩
  have hc (a k : d.K) : Commute (a : G) (b k) :=
    (commutator_eq_bot_iff_le_centralizer.mp d.commuting a.property _ (hbL k)).symm
  let f : d.K →* G := (d.K.subtype.noncommCoprod b hc).comp
    ((MonoidHom.id d.K).prod (MonoidHom.id d.K))
  have hfval (k : d.K) : f k = (k : G) * b k := rfl
  have hfinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro k hk
    have he : (k : G) = (b k)⁻¹ := mul_eq_one_iff_eq_inv.mp (show (k : G) * b k = 1 from hk)
    have hkL : (k : G) ∈ L := by rw [he]; exact L.inv_mem (hbL k)
    have hd := disjoint_iff.mp (disjoint_of_commuting_of_center_eq_bot d.commuting d.factor_center_eq_bot)
    have hk1 : (k : G) = 1 := mem_bot.mp (hd ▸ (show (k : G) ∈ d.K ⊓ L from ⟨k.property, hkL⟩))
    exact Subtype.ext hk1
  have hfC : f.range ≤ centralizer ({i} : Set G) := by
    rintro _ ⟨k, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh : i * f k * i⁻¹ = f k := by
      rw [hfval]
      change i * ((k : G) * (i * (k : G) * i⁻¹)) * i⁻¹ =
        (k : G) * (i * (k : G) * i⁻¹)
      calc
        _ = (i * (k : G) * i⁻¹) * ((i * i) * (k : G) * (i * i)⁻¹) := by group
        _ = (i * (k : G) * i⁻¹) * (k : G) := by rw [← pow_two, hi2]; simp
        _ = _ := (hc k k).eq.symm
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hfKg := image_le_conjugate d g f hfC
  let tx : d.K := ⟨d.x⁻¹ * d.t * d.x, d.crossing_mark⟩
  have htx : orderOf (tx : G) = 2 := by
    simpa only [MulAut.conj_apply, inv_inv] using
      ((MulAut.conj d.x⁻¹).orderOf_eq d.t).trans d.t_order
  have htxK : orderOf tx = 2 := (orderOf_coe tx).symm.trans htx
  have hfw : orderOf (f tx) = 2 := (orderOf_injective f hfinj tx).trans htxK
  have hbtx : orderOf (b tx) = 2 := ((MulAut.conj i).orderOf_eq (tx : G)).trans htx
  have hzw : IsConj d.z (f tx) := d.diagonal_involution_conjugate tx.property (hbL tx) htx hbtx
  obtain ⟨a, ha, he⟩ := mem_map.mp (hfKg ⟨tx, rfl⟩)
  have hoa : orderOf a = 2 := ((MulAut.conj g⁻¹).orderOf_eq a).symm.trans
    ((congrArg orderOf he).trans hfw)
  obtain ⟨m, _, hm⟩ := d.factor_involution_conjugate hoa (Or.inl ha)
  have hta : IsConj d.t a := isConj_iff.mpr ⟨m, hm⟩
  have haw : IsConj a (f tx) := isConj_iff.mpr ⟨g⁻¹, he⟩
  exact d.nonfusion ((hta.trans haw).trans hzw.symm)

end CFSG.Quasithin.Chapter2.PSL2PairSource.Incoming

end
