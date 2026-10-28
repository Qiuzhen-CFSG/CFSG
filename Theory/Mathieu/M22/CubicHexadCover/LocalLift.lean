module
public import Theory.Mathieu.M22.ValueBoundParabolics.OddCoverLifting

/-!
# Invariant cubic lifts through an odd central cover

A cubic local subgroup with two-core quotient S₃ splits canonically from an
odd central kernel. Its characteristic two-generated complement contains
the chosen Sylow subgroup, has relative index three, and is fixed by every
compatible automorphism preserving the local subgroup. This lifts the
marked M₂₂ hexad pair in Aschbacher--Smith 14.3.6(6), printed p.994.
-/

public section
open Subgroup
namespace Sporadic.Mathieu.CubicHexadCover
open M22ValueBound.OddCoverLifting
variable {E H : Type} [Group E] [Finite E] [Group H] [Finite H]

omit [Finite E] in
private theorem characteristic_image_invariant (A : Subgroup E) (D : Subgroup A)
    [D.Characteristic] (a : MulAut E) (ha : A.map a.toMonoidHom = A) :
    (D.map A.subtype).map a.toMonoidHom = D.map A.subtype := by
  let b : MulAut A := (a.subgroupMap A).trans (MulEquiv.subgroupCongr ha)
  have hb := characteristic_iff_map_eq.mp (inferInstance : D.Characteristic) b
  have hh := congrArg (Subgroup.map A.subtype) hb
  rw [map_map] at hh
  rw [map_map]
  exact hh

/-- The canonical complement above a cubic overgroup contains the specified
Sylow and preserves every compatible automorphism fixing that overgroup. -/
theorem exists_invariant_cubic_lift
    (f : E →* H) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (ho : Odd (Nat.card f.ker))
    (P : Sylow 2 E) (J : Subgroup H)
    (hPJ : (P : Subgroup E).map f ≤ J)
    (hi : ((P : Subgroup E).map f).relIndex J = 3)
    (eJ : (J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) :
    ∃ L : Subgroup E, (P : Subgroup E) ≤ L ∧ L.map f = J ∧
      (P : Subgroup E).relIndex L = 3 ∧
      ∀ (a : MulAut E) (b : MulAut H),
        (∀ x, b (f x) = f (a x)) → J.map b.toMonoidHom = J →
        L.map a.toMonoidHom = L := by
  let A := J.comap f
  let g := f.subgroupComap J
  have hg : Function.Surjective g := f.subgroupComap_surjective_of_surjective J hf
  have hPA : (P : Subgroup E) ≤ A := (map_le_iff_le_comap).mp hPJ
  have hgc : g.ker ≤ center A := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_center_iff.mp (hc (congrArg Subtype.val hx)) y
  have hko : Odd (Nat.card g.ker) := by
    have hdiv : Nat.card g.ker ∣ Nat.card f.ker := by
      let k : g.ker →* f.ker := (A.subtype.comp g.ker.subtype).codRestrict f.ker
        (fun x => congrArg Subtype.val x.property)
      apply card_dvd_of_injective k
      intro x y hh
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : f.ker => (z : E)) hh
    exact ho.of_dvd_nat hdiv
  obtain ⟨D,hchar,hcomp⟩ := oddCentralSplitting_three A J g hg hgc hko eJ
  let := hchar
  let ed : D ≃* J := hcomp.symm.QuotientMulEquiv.symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)
  have hDgen : twoGenerated D = ⊤ := by
    apply map_injective (f := ed.toMonoidHom) ed.injective
    rw [twoGenerated_map_equiv ed,twoGenerated_of_symmetric_twoCore eJ,
      map_top_of_surjective _ ed.surjective]
  have hDtwo : D = twoGenerated A := complement_eq_twoGenerated _ _ hgc hko hcomp hDgen
  have hPD : (P : Subgroup E).subgroupOf A ≤ D := by
    rw [hDtwo]
    exact isPGroup_le_twoGenerated _ P.isPGroup'.comap_subtype
  let L := D.map A.subtype
  have hPL : (P : Subgroup E) ≤ L := by
    have hh := map_mono (f := A.subtype) hPD
    rwa [map_subgroupOf_eq_of_le hPA] at hh
  have hDg : D.map g = ⊤ := by
    have hh := congrArg (Subgroup.map g) hcomp.sup_eq_top
    rw [Subgroup.map_sup,show g.ker.map g = ⊥ from (Subgroup.map_eq_bot_iff _).mpr le_rfl,
      bot_sup_eq,map_top_of_surjective _ hg] at hh
    exact hh
  have hLf : L.map f = J := by
    have hh := congrArg (Subgroup.map J.subtype) hDg
    rw [map_map,←MonoidHom.range_eq_map,range_subtype] at hh
    change D.map (f.comp A.subtype) = J at hh
    simpa only [L,map_map] using hh
  have hinj : Function.Injective (f.comp L.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro l hl
    obtain ⟨d,hd,hed⟩ := l.property
    apply Subtype.ext
    have hdker : d ∈ g.ker := by
      apply Subtype.ext
      change f (A.subtype d) = 1
      rw [hed]
      exact hl
    have hd1 : d = 1 := hcomp.disjoint.le_bot ⟨hdker,hd⟩
    calc
      (l : E) = A.subtype d := hed.symm
      _ = 1 := by rw [hd1,map_one]
  have hindex : (P : Subgroup E).relIndex L = 3 := by
    have hh := relIndex_map_map_of_injective (f := f.comp L.subtype)
      ((P : Subgroup E).subgroupOf L) (⊤ : Subgroup L) hinj
    have hPmap : ((P : Subgroup E).subgroupOf L).map (f.comp L.subtype) =
        (P : Subgroup E).map f := by
      rw [←map_map,map_subgroupOf_eq_of_le hPL]
    have htopmap : (⊤ : Subgroup L).map (f.comp L.subtype) = J := by
      rw [←map_map,←MonoidHom.range_eq_map,range_subtype]
      exact hLf
    rw [hPmap,htopmap,relIndex_top_right] at hh
    exact hh.symm.trans hi
  refine ⟨L,hPL,hLf,hindex,?_⟩
  intro a b he hbJ
  apply characteristic_image_invariant A D a
  have hpre : A.map a.toMonoidHom ≤ A := by
    rintro x ⟨y,hy,rfl⟩
    change f (a y) ∈ J
    rw [←he]
    exact hbJ ▸ mem_map_of_mem b.toMonoidHom hy
  exact eq_of_le_of_card_ge hpre (Nat.le_of_eq
    (Nat.card_congr (A.equivMapOfInjective a.toMonoidHom a.injective).toEquiv))

end Sporadic.Mathieu.CubicHexadCover
