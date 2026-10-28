module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Action

/-!
# Lifting the star factors into the supplied five-group

The restriction P → P* of H → H/O₂(H) is an isomorphism for a five-subgroup
P. Pull back a subgroup of P* along its inverse and then embed it into G.
The result lies in P, has exactly the prescribed star image, and has the
same order. All maps are the actual inclusion and quotient maps.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951. This is the transport needed after constructing the
order-five factors in the faithful star action; it asserts no such
factorization exists by itself.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
variable {G : Type*} [Group G] {H P : Subgroup G}

noncomputable def liftFiveFactor (hPH : P ≤ H) (hP : IsPGroup 5 P)
    (X : Subgroup (Source.Hstar H)) : Subgroup G :=
  ((X.subgroupOf (Source.starImage H P)).map (fiveStarEquiv hPH hP).symm.toMonoidHom).map
    P.subtype

theorem liftFiveFactor_le (hPH : P ≤ H) (hP : IsPGroup 5 P)
    (X : Subgroup (Source.Hstar H)) : liftFiveFactor hPH hP X ≤ P := map_subtype_le _

theorem starImage_liftFiveFactor (hPH : P ≤ H) (hP : IsPGroup 5 P)
    (X : Subgroup (Source.Hstar H)) (hX : X ≤ Source.starImage H P) :
    Source.starImage H (liftFiveFactor hPH hP X) = X := by
  ext x
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨p, hp, he⟩ := hh
    obtain ⟨y, hy, hye⟩ := hp
    have hhy : (h : G) = ((fiveStarEquiv hPH hP).symm y : G) :=
      he.symm.trans (congrArg Subtype.val hye.symm)
    have hs : QuotientGroup.mk' (pCore 2 H) h = (y : Source.Hstar H) := by
      have heh : h = inclusion hPH ((fiveStarEquiv hPH hP).symm y) := Subtype.ext hhy
      rw [heh, ← fiveStarEquiv_apply hPH hP]
      exact congrArg Subtype.val ((fiveStarEquiv hPH hP).apply_symm_apply y)
    exact hs ▸ hy
  · intro hx
    let y : Source.starImage H P := ⟨x, hX hx⟩
    let p := (fiveStarEquiv hPH hP).symm y
    refine ⟨inclusion hPH p, ?_, ?_⟩
    · exact mem_map_of_mem P.subtype (mem_map_of_mem (fiveStarEquiv hPH hP).symm.toMonoidHom hx)
    · rw [← fiveStarEquiv_apply hPH hP]
      exact congrArg Subtype.val ((fiveStarEquiv hPH hP).apply_symm_apply y)

theorem liftFiveFactor_card (hPH : P ≤ H) (hP : IsPGroup 5 P)
    (X : Subgroup (Source.Hstar H)) (hX : X ≤ Source.starImage H P) :
    Nat.card (liftFiveFactor hPH hP X) = Nat.card X := by
  let e := (fiveStarEquiv hPH hP).symm
  let E := X.subgroupOf (Source.starImage H P)
  have he : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have hp : Nat.card ((E.map e.toMonoidHom).map P.subtype) = Nat.card (E.map e.toMonoidHom) :=
    (Nat.card_congr ((E.map e.toMonoidHom).equivMapOfInjective P.subtype
      P.subtype_injective).toEquiv).symm
  exact hp.trans (he.trans (Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv))
end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
