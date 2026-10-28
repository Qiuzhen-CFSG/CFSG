module
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow
public import Theory.GroupTheory.CentralizerEquivBounds

/-!
# Conjugacy from Sylow centers of order two

Sylow conjugacy and uniqueness of the nonidentity element of each Sylow
center put all nonidentity two-central elements in one conjugacy class.
Consequently maximality of one marked centralizer proves maximality of all
of them. The Held and Rudvalis ordinary-component rows use this transport
with their literal certified central involutions.
Source: the Sylow argument in Aschbacher--Smith 15.1.20(3d), pp.1096--1097.
-/

public section
open Subgroup
namespace Theory.GroupTheory.DoubleCoverCentralizer
variable {H : Type*} [Group H] [Finite H]

/-- When every Sylow two-center has order two, all nonidentity two-central
 elements are conjugate. -/
theorem TwoCentral.isConj_of_center_card_two {u v : H}
    (hu : TwoCentral u) (hv : TwoCentral v) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hcard : ∀ P : Sylow 2 H, Nat.card (center P) = 2) : IsConj u v := by
  obtain ⟨P,huP,huc⟩ := hu
  obtain ⟨Q,hvQ,hvc⟩ := hv
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H P Q
  have he : ((g • P : Sylow 2 H) : Subgroup H) = Q :=
    congrArg (fun R : Sylow 2 H => (R : Subgroup H)) hg
  let e : P ≃* Q := (P.equivSMul g).trans (MulEquiv.subgroupCongr he)
  let a : center Q := (centerCongr e) ⟨⟨u,huP⟩,huc⟩
  let b : center Q := ⟨⟨v,hvQ⟩,hvc⟩
  have ha1 : a ≠ 1 := by
    intro ha
    have hh := (centerCongr e).injective (ha.trans (map_one (centerCongr e)).symm)
    exact hu1 (congrArg (fun x : center P => ((x : P) : H)) hh)
  have hb1 : b ≠ 1 := fun hb => hv1 (congrArg (fun x : center Q => ((x : Q) : H)) hb)
  obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1 : center Q)).mp (hcard Q)
  have hab : a = b := (hw a ha1).trans (hw b hb1).symm
  exact isConj_iff.mpr ⟨g, congrArg (fun x : center Q => ((x : Q) : H)) hab⟩

/-- Maximality of one nonidentity two-central centralizer transfers to every
such element when Sylow centers have order two. -/
theorem TwoCentral.centralizer_isCoatom_of_center_card_two {u v : H}
    (hu : TwoCentral u) (hv : TwoCentral v) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hcard : ∀ P : Sylow 2 H, Nat.card (center P) = 2)
    (hmax : IsCoatom (centralizer ({v} : Set H))) :
    IsCoatom (centralizer ({u} : Set H)) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (hu.isConj_of_center_card_two hv hu1 hv1 hcard)
  have he : (MulAut.conj g) u = v := hg
  exact (isCoatom_centralizer_equiv_iff (MulAut.conj g) u).mp (he.symm ▸ hmax)
end Theory.GroupTheory.DoubleCoverCentralizer
