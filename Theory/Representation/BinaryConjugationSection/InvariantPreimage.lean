module

public import Theory.Representation.BinaryConjugationSection
public import Mathlib.RepresentationTheory.Subrepresentation
public import Theory.ElementaryAbelian.VectorSpace

/-!
# Invariant preimages in an actual binary conjugation section

An invariant subspace of a marked section R/V pulls back to a subgroup of
the original R. Restriction keeps the actual coordinate quotient and ambient
conjugation action. A transitive nonzero orbit with one involutory lift then
makes the full preimage elementary, by the central elementary kernel lemma.

Source application: Aschbacher–Smith 14.3.18(4), printed p.996. The natural
S₃ planes and their chosen involutions remain the exact preceding inputs.
-/

@[expose] public section
noncomputable section

namespace Representation.BinaryConjugationSection
open Subgroup
variable {G : Type*} [Group G] {H R V : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} (d : BinaryConjugationSection H R V ρ)

def invariantPreimage (P : Subrepresentation ρ) : Subgroup G :=
  (P.toSubmodule.toAddSubgroup.toSubgroup.comap d.coordinates).map R.subtype

theorem mem_invariantPreimage (P : Subrepresentation ρ) (x : G) :
    x ∈ d.invariantPreimage P ↔ ∃ hx : x ∈ R,
      (d.coordinates ⟨x, hx⟩).toAdd ∈ P.toSubmodule := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩
  · rintro ⟨hx, hP⟩
    exact ⟨⟨x, hx⟩, hP, rfl⟩

theorem invariantPreimage_le (P : Subrepresentation ρ) : d.invariantPreimage P ≤ R :=
  map_subtype_le _

theorem kernel_le_invariantPreimage (P : Subrepresentation ρ) : V ≤ d.invariantPreimage P := by
  intro x hx
  refine (d.mem_invariantPreimage P x).mpr ⟨d.kernel_le hx, ?_⟩
  have he := (d.coordinates_eq_one_iff ⟨x,d.kernel_le hx⟩).mpr hx
  rw [he]
  exact P.toSubmodule.zero_mem

theorem invariantPreimage_normalized (P : Subrepresentation ρ) :
    H ≤ normalizer (d.invariantPreimage P : Set G) := by
  intro h hh
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    obtain ⟨hxR,hxP⟩ := (d.mem_invariantPreimage P x).mp hx
    refine (d.mem_invariantPreimage P _).mpr
      ⟨(mem_normalizer_iff.mp (d.normalized hh) x).mp hxR, ?_⟩
    rw [d.equivariant ⟨h,hh⟩ ⟨x,hxR⟩]
    exact P.apply_mem_toSubmodule ⟨h,hh⟩ hxP
  · intro hx
    obtain ⟨hxR,hxP⟩ := (d.mem_invariantPreimage P _).mp hx
    have hxR' : x ∈ R := (mem_normalizer_iff.mp (d.normalized hh) x).mpr hxR
    refine (d.mem_invariantPreimage P _).mpr ⟨hxR', ?_⟩
    have hi := P.apply_mem_toSubmodule (⟨h,hh⟩ : H)⁻¹ hxP
    rw [d.equivariant ⟨h,hh⟩ ⟨x,hxR'⟩] at hi
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using hi

def invariantCoordinates (P : Subrepresentation ρ) :
    d.invariantPreimage P →* Multiplicative P.toSubmodule where
  toFun a := Multiplicative.ofAdd
    ⟨(d.coordinates ⟨a,d.invariantPreimage_le P a.property⟩).toAdd,
      (d.mem_invariantPreimage P a).mp a.property |>.choose_spec⟩
  map_one' := by apply Subtype.ext; exact congrArg Multiplicative.toAdd (map_one d.coordinates)
  map_mul' a b := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (map_mul d.coordinates
      ⟨a,d.invariantPreimage_le P a.property⟩ ⟨b,d.invariantPreimage_le P b.property⟩)

def invariantSection (P : Subrepresentation ρ) :
    BinaryConjugationSection H (d.invariantPreimage P) V P.toRepresentation where
  section_le := (d.invariantPreimage_le P).trans d.section_le
  kernel_le := d.kernel_le_invariantPreimage P
  normalized := d.invariantPreimage_normalized P
  coordinates := d.invariantCoordinates P
  onto := by
    intro p
    obtain ⟨r,hr⟩ := d.onto (Multiplicative.ofAdd p.toAdd.val)
    have hp : (r : G) ∈ d.invariantPreimage P := by
      apply (d.mem_invariantPreimage P r).mpr
      refine ⟨r.property, ?_⟩
      rw [hr]
      exact p.toAdd.property
    refine ⟨⟨r,hp⟩, ?_⟩
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd hr
  kernel_eq := by
    ext a
    change d.invariantCoordinates P a = 1 ↔ (a : G) ∈ V
    rw [← d.coordinates_eq_one_iff ⟨a,d.invariantPreimage_le P a.property⟩]
    constructor
    · intro he
      exact congrArg (fun x : Multiplicative P.toSubmodule => Multiplicative.ofAdd x.toAdd.val) he
    · intro he
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd he
  equivariant h a := by
    apply Subtype.ext
    exact d.equivariant h ⟨a,d.invariantPreimage_le P a.property⟩

theorem invariantPreimage_elementary (P : Subrepresentation ρ)
    (hcentral : V ≤ centralizer (R : Set G))
    (hsquare : ∀ v ∈ V, v ^ 2 = 1)
    (htrans : ∀ u v : P.toSubmodule, u ≠ 0 → v ≠ 0 →
      ∃ h : H, P.toRepresentation h u = v)
    (a : R) (ha : a ^ 2 = 1) (haP : (d.coordinates a).toAdd ∈ P.toSubmodule)
    (haV : d.coordinates a ≠ 1) : IsElementaryAbelian 2 (d.invariantPreimage P) := by
  apply (d.invariantSection P).elementary_of_transitive
    (hcentral.trans (centralizer_le (d.invariantPreimage_le P))) hsquare _ htrans
  have hap : (a : G) ∈ d.invariantPreimage P :=
    (d.mem_invariantPreimage P a).mpr ⟨a.property,haP⟩
  refine ⟨⟨a,hap⟩, Subtype.ext (show (a : G) ^ 2 = 1 from congrArg (fun x : R => (x : G)) ha), ?_⟩
  intro he
  exact haV (congrArg (fun x : Multiplicative P.toSubmodule => Multiplicative.ofAdd x.toAdd.val) he)

theorem invariantPreimage_card (P : Subrepresentation ρ) :
    Nat.card (d.invariantPreimage P) = Nat.card P.toSubmodule * Nat.card V :=
  (d.invariantSection P).card_section

theorem invariantPreimage_inf (P Q : Subrepresentation ρ)
    (h : Disjoint P.toSubmodule Q.toSubmodule) :
    d.invariantPreimage P ⊓ d.invariantPreimage Q = V := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxR,hxP⟩ := (d.mem_invariantPreimage P x).mp hx.1
    obtain ⟨_,hxQ⟩ := (d.mem_invariantPreimage Q x).mp hx.2
    apply (d.coordinates_eq_one_iff ⟨x,hxR⟩).mp
    exact Multiplicative.toAdd.injective (Submodule.disjoint_def.mp h _ hxP hxQ)
  · exact le_inf (d.kernel_le_invariantPreimage P) (d.kernel_le_invariantPreimage Q)

theorem invariantPreimage_sup (P Q : Subrepresentation ρ)
    (h : P.toSubmodule ⊔ Q.toSubmodule = ⊤) :
    d.invariantPreimage P ⊔ d.invariantPreimage Q = R := by
  apply le_antisymm (sup_le (d.invariantPreimage_le P) (d.invariantPreimage_le Q))
  intro x hx
  have hm : (d.coordinates ⟨x,hx⟩).toAdd ∈ P.toSubmodule ⊔ Q.toSubmodule := by
    rw [h]
    trivial
  obtain ⟨p,hp,q,hq,hpq⟩ := Submodule.mem_sup.mp hm
  obtain ⟨a,ha⟩ := d.onto (Multiplicative.ofAdd p)
  obtain ⟨b,hb⟩ := d.onto (Multiplicative.ofAdd q)
  have hap : (a : G) ∈ d.invariantPreimage P := by
    apply (d.mem_invariantPreimage P a).mpr
    exact ⟨a.property, by rw [ha]; exact hp⟩
  have hbq : (b : G) ∈ d.invariantPreimage Q := by
    apply (d.mem_invariantPreimage Q b).mpr
    exact ⟨b.property, by rw [hb]; exact hq⟩
  let c : R := (a*b)⁻¹ * ⟨x,hx⟩
  have hc : (c : G) ∈ V := by
    apply (d.coordinates_eq_one_iff c).mp
    change d.coordinates ((a*b)⁻¹ * ⟨x,hx⟩) = 1
    rw [map_mul,map_inv,map_mul,ha,hb]
    have he : Multiplicative.ofAdd p * Multiplicative.ofAdd q =
        d.coordinates ⟨x,hx⟩ := Multiplicative.toAdd.injective hpq
    rw [he,inv_mul_cancel]
  have hc' : (c : G) ∈ d.invariantPreimage P ⊔ d.invariantPreimage Q :=
    (show d.invariantPreimage P ≤ d.invariantPreimage P ⊔ d.invariantPreimage Q from le_sup_left)
      ((d.kernel_le_invariantPreimage P) hc)
  have hm' := (d.invariantPreimage P ⊔ d.invariantPreimage Q).mul_mem
    ((d.invariantPreimage P ⊔ d.invariantPreimage Q).mul_mem
      ((show d.invariantPreimage P ≤ d.invariantPreimage P ⊔ d.invariantPreimage Q from le_sup_left) hap)
      ((show d.invariantPreimage Q ≤ d.invariantPreimage P ⊔ d.invariantPreimage Q from le_sup_right) hbq)) hc'
  simpa only [c,Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_cancel_left] using hm'

theorem invariantPreimage_normal (P : Subrepresentation ρ) :
    ((d.invariantPreimage P).subgroupOf H).Normal :=
  (normal_subgroupOf_iff_le_normalizer
    ((d.invariantPreimage_le P).trans d.section_le)).mpr (d.invariantPreimage_normalized P)

/-- Two complementary natural planes with involutory representatives give
the two actual elementary factors of order sixteen, with their common
four-group and their ambient normality retained. -/
theorem elementary_plane_pair (P Q : Subrepresentation ρ)
    (hPQ : IsCompl P.toSubmodule Q.toSubmodule)
    (hPcard : Nat.card P.toSubmodule = 4) (hQcard : Nat.card Q.toSubmodule = 4)
    (hVcard : Nat.card V = 4)
    (hcentral : V ≤ centralizer (R : Set G)) (hsquare : ∀ v ∈ V, v ^ 2 = 1)
    (hPtrans : ∀ u v : P.toSubmodule, u ≠ 0 → v ≠ 0 →
      ∃ h : H, P.toRepresentation h u = v)
    (hQtrans : ∀ u v : Q.toSubmodule, u ≠ 0 → v ≠ 0 →
      ∃ h : H, Q.toRepresentation h u = v)
    (a b : R) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (haP : (d.coordinates a).toAdd ∈ P.toSubmodule)
    (hbQ : (d.coordinates b).toAdd ∈ Q.toSubmodule)
    (haV : d.coordinates a ≠ 1) (hbV : d.coordinates b ≠ 1) :
    IsElementaryAbelian 2 (d.invariantPreimage P) ∧
      IsElementaryAbelian 2 (d.invariantPreimage Q) ∧
      Nat.card (d.invariantPreimage P) = 16 ∧
      Nat.card (d.invariantPreimage Q) = 16 ∧
      d.invariantPreimage P ⊓ d.invariantPreimage Q = V ∧
      d.invariantPreimage P ⊔ d.invariantPreimage Q = R ∧
      ((d.invariantPreimage P).subgroupOf H).Normal ∧
      ((d.invariantPreimage Q).subgroupOf H).Normal := by
  refine ⟨d.invariantPreimage_elementary P hcentral hsquare hPtrans a ha haP haV,
    d.invariantPreimage_elementary Q hcentral hsquare hQtrans b hb hbQ hbV,
    ?_, ?_, d.invariantPreimage_inf P Q hPQ.disjoint,
    d.invariantPreimage_sup P Q hPQ.sup_eq_top,
    d.invariantPreimage_normal P, d.invariantPreimage_normal Q⟩
  · rw [d.invariantPreimage_card,hPcard,hVcard]
  · rw [d.invariantPreimage_card,hQcard,hVcard]

end Representation.BinaryConjugationSection
