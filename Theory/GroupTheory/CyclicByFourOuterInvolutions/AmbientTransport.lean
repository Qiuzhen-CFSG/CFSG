module

public import Theory.GroupTheory.CyclicByFourOuterInvolutions
public import Mathlib.GroupTheory.Sylow

/-!
# Faithful ambient transport of cyclic-by-four coordinates

Coordinates in one Sylow subgroup transport by conjugacy to every Sylow.
If a faithful subgroup contains the distinguished normal subgroup and has
an outer element in its Sylow, the four normal forms force its Sylow image
to be a full Sylow of the larger group. Indeed, the inner generators lift
by Sylow maximality, and the outer element supplies the remaining coset.

The inner reflection does not centralize the cyclic generator, whose order
is twice the reflection exponent plus two. Thus a centralizing inner
involution lies in the cyclic subgroup and equals its marked half-power.
This identifies the original marked element when pulling back all coordinates.

Source application: Aschbacher--Smith E.1.14(7), printed p.214, and
Aschbacher (1982), Lemma 4.11. The argument here is general Sylow theory
and the explicit relations, without any unitary model assumption.
-/

public section

open Subgroup
namespace Theory.GroupTheory.CyclicByFourCoordinates
variable {G H : Type*} [Group G] [Group H] {L T : Subgroup G} {z : G}

/-- Transport every generator, relation and normal form through an actual equivalence. -/
def mapEquiv (d : CyclicByFourCoordinates L T z) (e : G ≃* H) :
    CyclicByFourCoordinates (L.map e.toMonoidHom) (T.map e.toMonoidHom) (e z) where
  a := e d.a
  b := e d.b
  c := e d.c
  n := d.n
  a_order := (e.orderOf_eq d.a).trans d.a_order
  a_inner := mem_map_of_mem _ d.a_inner
  a_mem := mem_map_of_mem _ d.a_mem
  b_inner := mem_map_of_mem _ d.b_inner
  b_mem := mem_map_of_mem _ d.b_mem
  c_mem := mem_map_of_mem _ d.c_mem
  c_outer := by
    rintro ⟨x, hx, he⟩
    exact d.c_outer (e.injective he ▸ hx)
  c_sq := by rw [← map_pow, d.c_sq, map_one]
  b_action := by simpa only [map_mul, map_pow, map_inv] using congrArg e d.b_action
  c_action := by simpa only [map_mul, map_pow, map_inv] using congrArg e d.c_action
  marked := by simpa only [map_pow] using congrArg e d.marked
  cover := by
    rintro t ⟨x, hx, rfl⟩
    obtain ⟨i, hi | hi | hi | hi⟩ := d.cover x hx
    · exact ⟨i, Or.inl (by simpa only [map_zpow, MulEquiv.coe_toMonoidHom] using congrArg e hi)⟩
    · exact ⟨i, Or.inr (Or.inl (by simpa only [map_zpow, map_mul, MulEquiv.coe_toMonoidHom] using congrArg e hi))⟩
    · exact ⟨i, Or.inr (Or.inr (Or.inl (by simpa only [map_zpow, map_mul, MulEquiv.coe_toMonoidHom] using congrArg e hi)))⟩
    · exact ⟨i, Or.inr (Or.inr (Or.inr (by simpa only [map_zpow, map_mul, MulEquiv.coe_toMonoidHom] using congrArg e hi)))⟩

/-- An inner involution commuting with the rotation is its marked half-power. -/
theorem eq_marked_of_inner_involution [Finite G] (d : CyclicByFourCoordinates L T z)
    {w : G} (hwL : w ∈ L) (hwT : w ∈ T) (hw : orderOf w = 2)
    (hc : Commute w d.a) : w = z := by
  have hm : 4 ≤ 2 ^ (d.n + 2) := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (d.n + 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hao : orderOf d.a = 2 ^ (d.n + 2) * 2 := by
    rw [d.a_order]; ring
  have hwC : w ∈ zpowers d.a := by
    obtain ⟨i, hi | hi⟩ := d.inner_cover w hwT hwL
    · rw [hi]; exact zpow_mem (mem_zpowers _) i
    · have hba : d.b * d.a = d.a * d.b := by
        apply mul_left_cancel (a := d.a ^ i)
        calc
          d.a ^ i * (d.b * d.a) = (d.a ^ i * d.b) * d.a := by group
          _ = d.a * (d.a ^ i * d.b) := by rw [← hi]; exact hc.eq
          _ = d.a ^ i * (d.a * d.b) := by group
      have he : d.a ^ (2 ^ (d.n + 2) - 1) = d.a ^ 1 := by
        rw [pow_one, ← d.b_action, hba, mul_inv_cancel_right]
      have hh := pow_injOn_Iio_orderOf (x := d.a)
        (show 2 ^ (d.n + 2) - 1 < orderOf d.a by rw [hao]; omega)
        (show 1 < orderOf d.a by rw [hao]; omega) he
      omega
  have hzC : z ∈ zpowers d.a := by
    simpa only [d.marked] using (zpowers d.a).pow_mem (mem_zpowers d.a) (2 ^ (d.n + 2))
  exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
    (x := (⟨w, hwC⟩ : zpowers d.a)) (y := (⟨z, hzC⟩ : zpowers d.a))
    (by simpa only [orderOf_mk] using hw) (by simpa only [orderOf_mk] using d.marked_order))


/-- Conjugacy transports the coordinates relative to the same normal subgroup. -/
theorem on_sylow [Finite G] [L.Normal] (S₀ S : Sylow 2 G)
    (d : CyclicByFourCoordinates L (S₀ : Subgroup G) z) :
    ∃ w : G, Nonempty (CyclicByFourCoordinates L (S : Subgroup G) w) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ S
  have hL : L.map (MulAut.conj g).toMonoidHom = L := Normal.conj_smul_eq_self g L
  have hS : (S₀ : Subgroup G).map (MulAut.conj g).toMonoidHom = (S : Subgroup G) := by
    change ((g • S₀ : Sylow 2 G) : Subgroup G) = _
    rw [hg]
  exact ⟨MulAut.conj g z, ⟨by simpa only [hL, hS] using d.mapEquiv (MulAut.conj g)⟩⟩

/-- A faithful ambient subgroup containing the normal subgroup has full Sylow
image as soon as its Sylow has an outer element. The conclusion records the
literal subgroup image together with the transported coordinates. -/
theorem sylow_image_coordinates [Finite H] (f : G →* H) (hf : Function.Injective f)
    (N : Subgroup H) [N.Normal] (hLN : L.map f = N)
    (S₀ : Sylow 2 H) {v : H} (d : CyclicByFourCoordinates N (S₀ : Subgroup H) v)
    (T : Sylow 2 G) (hout : ¬ (T : Subgroup G) ≤ L) :
    ∃ (S : Sylow 2 H) (w : H),
      (T : Subgroup G).map f = (S : Subgroup H) ∧
      Nonempty (CyclicByFourCoordinates N (S : Subgroup H) w) := by
  classical
  obtain ⟨S, hS⟩ := T.exists_comap_eq_of_injective hf
  obtain ⟨w, ⟨dS⟩⟩ := d.on_sylow S₀ S
  have hTS : (T : Subgroup G).map f ≤ (S : Subgroup H) :=
    map_le_iff_le_comap.mpr hS.ge
  have hinner (x : H) (hxN : x ∈ N) (hxS : x ∈ S) : x ∈ (T : Subgroup G).map f := by
    obtain ⟨y, hy, rfl⟩ := mem_map.mp (hLN.symm ▸ hxN)
    exact mem_map_of_mem f (show y ∈ (T : Subgroup G) from hS ▸ hxS)
  have ha := hinner dS.a dS.a_inner dS.a_mem
  have hb := hinner dS.b dS.b_inner dS.b_mem
  obtain ⟨t, ht, hto⟩ := Set.not_subset.mp hout
  have hfo : f t ∉ N := by
    intro h
    obtain ⟨x, hx, he⟩ := mem_map.mp (hLN.symm ▸ h)
    exact hto (hf he ▸ hx)
  have hft : f t ∈ (T : Subgroup G).map f := mem_map_of_mem f ht
  have hc : dS.c ∈ (T : Subgroup G).map f := by
    obtain ⟨i, hi | hi | hi | hi⟩ := dS.cover (f t) (hTS hft)
    · exact (hfo (hi ▸ N.zpow_mem dS.a_inner i)).elim
    · exact (hfo (hi ▸ N.mul_mem (N.zpow_mem dS.a_inner i) dS.b_inner)).elim
    · have h := ((T : Subgroup G).map f).mul_mem
        (((T : Subgroup G).map f).inv_mem (((T : Subgroup G).map f).zpow_mem ha i)) hft
      simpa only [hi, inv_mul_cancel_left] using h
    · have h := ((T : Subgroup G).map f).mul_mem
        (((T : Subgroup G).map f).inv_mem
          (((T : Subgroup G).map f).mul_mem (((T : Subgroup G).map f).zpow_mem ha i) hb)) hft
      simpa only [hi, inv_mul_cancel_left] using h
  refine ⟨S, w, le_antisymm hTS ?_, ⟨dS⟩⟩
  intro s hs
  obtain ⟨i, hi | hi | hi | hi⟩ := dS.cover s hs
  · exact hi ▸ ((T : Subgroup G).map f).zpow_mem ha i
  · exact hi ▸ ((T : Subgroup G).map f).mul_mem (((T : Subgroup G).map f).zpow_mem ha i) hb
  · exact hi ▸ ((T : Subgroup G).map f).mul_mem (((T : Subgroup G).map f).zpow_mem ha i) hc
  · exact hi ▸ ((T : Subgroup G).map f).mul_mem
      (((T : Subgroup G).map f).mul_mem (((T : Subgroup G).map f).zpow_mem ha i) hb) hc

/-- Pull coordinates back to a faithful ambient Sylow, identifying its given
centralizing inner involution with the canonical marked element. -/
theorem of_faithful_sylow [Finite H] (f : G →* H) (hf : Function.Injective f)
    (N : Subgroup H) [N.Normal] (hLN : L.map f = N)
    (S₀ : Sylow 2 H) {v : H} (d : CyclicByFourCoordinates N (S₀ : Subgroup H) v)
    (T : Sylow 2 G) (hout : ¬ (T : Subgroup G) ≤ L)
    (hz : orderOf z = 2) (hzL : z ∈ L) (hzT : z ∈ T)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    Nonempty (CyclicByFourCoordinates L (T : Subgroup G) z) := by
  obtain ⟨S, w, hS, ⟨dS⟩⟩ := d.sylow_image_coordinates f hf N hLN S₀ T hout
  have hzw : f z = w := by
    apply dS.eq_marked_of_inner_involution
    · rw [← hLN]; exact mem_map_of_mem f hzL
    · rw [← hS]; exact mem_map_of_mem f hzT
    · exact (orderOf_injective f hf z).trans hz
    · have haS : dS.a ∈ (T : Subgroup G).map f := by rw [hS]; exact dS.a_mem
      obtain ⟨a, ha, hae⟩ := mem_map.mp haS
      rw [← hae]
      exact (show Commute z a from (mem_centralizer_singleton_iff.mp (hTz ha)).symm).map f
  apply of_map f hf
  simpa only [hLN, hS, hzw] using dS

end Theory.GroupTheory.CyclicByFourCoordinates
