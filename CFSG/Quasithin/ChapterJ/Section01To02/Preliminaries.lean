module

public import CFSG.Quasithin.ChapterJ.Defs
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.PSL3Two.SmallModuleProperties

/-!
# Order and elementary-abelian steps for J.2

The genuine Ru1 actions give |V| = 8, |S| = 2¹¹ and |L| = 2¹⁴·21.
Once the center-order calculation in J.2.1 supplies |Z(T)| = 2, Ru2 gives
|U| = 32, |Q| = 2¹¹ and |H| = 2¹⁴·15. The compatible Sylow choice
then proves T ≤ L, the numerical step of J.2.1(1).

For J.2.2(2), the actual SL₂(4) action is transitive on nonzero vectors
of U/Z. Since V has eight elements and Z has two, V supplies a
square-one lift outside Z. Centrality of Z allows transport to every
coset, so U has exponent two. The final result constructs an actual
isomorphism U ≃ E₃₂.

The center-order calculation and the other structural assertions of J.2
are not assumptions of the type-Ru definition and are not asserted proved
here. The explicit |Z| = 2 premises must be discharged in section assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.1 and J.2.2(2), printed p.432 (PDF p.443).
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterJ
open Representation
variable {G : Type*} [Group G]

theorem le_conjugateSpan (H V : Subgroup G) : V ≤ conjugateSpan H V := by
  intro v hv
  apply (le_iSup (fun h : H => V.map (MulAut.conj (h : G)).toMonoidHom) 1)
  exact mem_map.mpr ⟨v, hv, by simp⟩

theorem RuOne.card_V {L V : Subgroup G} (r : RuOne L V) : Nat.card V = 8 := by
  have h := r.natural.card_section
  norm_num [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector,
    Nat.card_fun, Nat.card_zmod] at h
  exact h

theorem RuOne.card_S {L V : Subgroup G} (r : RuOne L V) : Nat.card (L.pCoreIn 2) = 2048 := by
  have h := r.steinberg.card_section
  have hdim : Nat.card BinaryLinearThree.Steinberg = 256 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), BinaryLinearThree.finrank_steinberg]
    norm_num [Nat.card_zmod]
  rw [hdim, r.card_V] at h
  exact h

theorem RuOne.card_L {L V : Subgroup G} (r : RuOne L V) : Nat.card L = 344064 := by
  rw [card_eq_card_quotient_mul_card_subgroup r.quotientMap.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      r.quotientMap r.quotient_surjective).toEquiv, r.quotient_kernel,
    Nat.card_congr (subgroupOfEquivOfLe (pCoreIn_le 2 L)).toEquiv,
    r.card_S, Matrix.PSL3Two.card_SL]

theorem RuTwo.card_U {V : Subgroup G} {T : Sylow 2 G} (r : RuTwo V T)
    (hZ : Nat.card (sylowCenter T) = 2) :
    Nat.card (conjugateSpan (centralizerOfSylowCenter T) V) = 32 := by
  have h := r.natural.card_section
  have hfour : Nat.card FourSpace = 16 := by
    rw [Nat.card_eq_fintype_card]
    exact SL2FourNatural.card_vector
  rw [hZ, hfour] at h
  exact h

theorem RuTwo.card_Q {V : Subgroup G} {T : Sylow 2 G} (r : RuTwo V T)
    (hZ : Nat.card (sylowCenter T) = 2) :
    Nat.card ((centralizerOfSylowCenter T).pCoreIn 2) = 2048 := by
  have h := r.six.card_section
  have hsix : Nat.card SixSpace = 64 := by norm_num [SixSpace, Nat.card_fun, Nat.card_zmod]
  rw [hsix, r.card_U hZ] at h
  exact h

theorem RuTwo.card_H {V : Subgroup G} {T : Sylow 2 G} (r : RuTwo V T)
    (hZ : Nat.card (sylowCenter T) = 2) : Nat.card (centralizerOfSylowCenter T) = 245760 := by
  rw [card_eq_card_quotient_mul_card_subgroup r.quotientMap.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      r.quotientMap r.quotient_surjective).toEquiv, r.quotient_kernel,
    Nat.card_congr (subgroupOfEquivOfLe (pCoreIn_le 2 _)).toEquiv, r.card_Q hZ]
  have hS5 : Nat.card S5 = 120 := by
    norm_num [S5, Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [hS5]

theorem RuTwo.transitive_natural {V : Subgroup G} {T : Sylow 2 G} (r : RuTwo V T)
    (u v : FourSpace) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ h : centralizerOfSylowCenter T,
      r.naturalAction.action (r.quotientMap h) u = v := by
  obtain ⟨g, hg⟩ := SL2FourNatural.transitive_nonzero u v hu hv
  obtain ⟨h, hh⟩ := r.quotient_surjective (r.naturalAction.marking g)
  exact ⟨h, by rw [hh, r.naturalAction.restriction]; exact hg⟩

variable [Finite G]

/-- The elementary-abelian assertion of J.2.2(2), after J.2.1 supplies |Z| = 2. -/
theorem TypeRuSetup.elementary_U_of_card_Z (d : TypeRuSetup G) (hZ : Nat.card d.Z = 2) :
    IsElementaryAbelian 2 d.U := by
  have hVU : d.V ≤ d.U := le_conjugateSpan d.H d.V
  have hseed : ∃ v : d.V, (v : G) ∉ d.Z := by
    by_contra! hn
    have hle : d.V ≤ d.Z := fun v hv => hn ⟨v, hv⟩
    have hc := card_le_of_le hle
    rw [d.ru1.card_V, hZ] at hc
    omega
  obtain ⟨v, hv⟩ := hseed
  apply d.ru2.natural.elementary_of_transitive
  · exact le_centralizer_iff.mpr d.ru2.natural.section_le
  · intro z hz
    have he := pow_card_eq_one' (x := (⟨z, hz⟩ : d.Z))
    rw [hZ] at he
    exact congrArg Subtype.val he
  · refine ⟨⟨v, hVU v.property⟩, ?_, ?_⟩
    · apply Subtype.ext
      exact congrArg (fun x : d.V => (x : G))
        (d.ru1.natural.square_eq_one_of_trivial_kernel rfl v)
    · exact fun he => hv ((d.ru2.natural.coordinates_eq_one_iff _).mp he)
  · exact d.ru2.transitive_natural

/-- The actual E₃₂ isomorphism in J.2.2(2), conditional only on J.2.1's center order. -/
theorem TypeRuSetup.equiv_U_of_card_Z (d : TypeRuSetup G) (hZ : Nat.card d.Z = 2) :
    Nonempty (d.U ≃* Multiplicative (Fin 5 → ZMod 2)) := by
  let := d.elementary_U_of_card_Z hZ
  have hdim : Module.finrank (ZMod 2) (Additive d.U) = 5 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive d.U)
    change Nat.card d.U = _ at hc
    simpa only [Nat.card_zmod, d.ru2.card_U hZ, show 2 ^ 5 = 32 by decide] using hc.symm
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive d.U) hdim
  exact ⟨b.equivFun.toAddEquiv.toMultiplicativeRight⟩

/-- The chosen Sylow group centralizes its own center. -/
theorem TypeRuSetup.T_le_H (d : TypeRuSetup G) : (d.T : Subgroup G) ≤ d.H := by
  intro t ht z hz
  obtain ⟨z, hz, rfl⟩ := hz
  exact (congrArg (fun x : d.T => (x : G)) ((mem_center_iff.mp hz) ⟨t, ht⟩)).symm

/-- The numerical Sylow step of J.2.1. -/
theorem TypeRuSetup.card_T_of_card_Z (d : TypeRuSetup G) (hZ : Nat.card d.Z = 2) :
    Nat.card d.T = 16384 := by
  have hc := (d.T.subtype d.T_le_H).card_eq_multiplicity
  have he : Nat.card (d.T.subtype d.T_le_H) = Nat.card d.T :=
    Nat.card_congr (subgroupOfEquivOfLe d.T_le_H).toEquiv
  rw [he, d.ru2.card_H hZ] at hc
  exact hc.trans (by decide +kernel)

/-- J.2.1(1) from the source-compatible Sylow choice and the center-order calculation. -/
theorem LocalSetup.T_le_L_of_card_Z (d : LocalSetup G)
    (hZ : Nat.card d.toTypeRuSetup.Z = 2) : (d.T : Subgroup G) ≤ d.L := by
  have hPL : Nat.card d.sylowInL = 16384 := by
    rw [d.sylowInL.card_eq_multiplicity, d.ru1.card_L]
    decide +kernel
  have he : (d.T : Subgroup G) ⊓ d.L = (d.T : Subgroup G) := by
    apply Subgroup.eq_of_le_of_card_ge inf_le_left
    rw [d.intersection_eq, card_map_of_injective d.L.subtype_injective,
      hPL, d.toTypeRuSetup.card_T_of_card_Z hZ]
  exact he.symm.le.trans inf_le_right

end CFSG.Quasithin.ChapterJ
