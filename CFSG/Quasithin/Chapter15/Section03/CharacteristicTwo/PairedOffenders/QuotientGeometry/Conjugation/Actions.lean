module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Conjugation.Semidihedral
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.RegularEven
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Dihedral

/-!
# Transporting conjugate markings through the two actual actions

A local coordinate diagram uses an action defined on S and an identification
 of its actual quotient with the canonical dihedral quotient. Its marked
 four-group is characterized by the parity of that action. Compatible actor
 and quotient conjugations, and a permutation relabeling of the two actions,
 therefore identify the second marking with the conjugate of the first.
The SD16 interchange yields the three source pairings; inner conjugation
 preserves the marking and gives equality of cases. The equal-image wrapper
 applies this to the original quotient map and proves its compatibility.

Source: Aschbacher–Smith, proof of 15.3.25, printed pp.1133–1134.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.ChapterB.Offenders
open CFSG.Quasithin.ChapterB.Offenders.Eight
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient.Conjugation

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Coordinates for an action defined just on the local actor group. In the
 application that group is S; no action on the module-swapping T is needed. -/
structure LocalCoordinates (f : G →* Perm) (q : G →* H) where
  action_le : f.range ≤ canonicalSylow
  quotientEquiv : H ≃* Quotient
  compatible (s : G) : quotientEquiv (q s) =
    quotientMap ⟨f s, action_le ⟨s, rfl⟩⟩

namespace LocalCoordinates
variable {f g : G →* Perm} {q : G →* H}

def marked (d : LocalCoordinates f q) : Subgroup H :=
  evenFour.map d.quotientEquiv.symm.toMonoidHom

instance (d : LocalCoordinates f q) : IsElementaryAbelian 2 d.marked :=
  IsElementaryAbelian.map d.quotientEquiv.symm.toMonoidHom

theorem card_marked (d : LocalCoordinates f q) : Nat.card d.marked = 4 :=
  (card_map_of_injective d.quotientEquiv.symm.injective).trans card_evenFour

theorem center_le_marked (d : LocalCoordinates f q) : center H ≤ d.marked := by
  rw [← map_center d.quotientEquiv.symm]
  exact map_mono center_le_evenFour

theorem image_eq (d : LocalCoordinates f q) (A : Subgroup G) :
    (A.map q).map d.quotientEquiv.toMonoidHom = quotientImage (A.map f) := by
  ext z
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨⟨f a, d.action_le ⟨a, rfl⟩⟩,
      mem_map_of_mem f ha, (d.compatible a).symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha, he⟩ := hx
    refine ⟨q a, mem_map_of_mem q ha, ?_⟩
    change d.quotientEquiv (q a) = quotientMap x
    rw [d.compatible]
    exact congrArg quotientMap (Subtype.ext he)

theorem position_of_realizes (d : LocalCoordinates f q) {A : Subgroup G}
    {c : EightCase} (hA : c.Realizes (A.map f)) : Position c d.marked (A.map q) := by
  have hle : A.map f ≤ canonicalSylow := (map_le_range f A).trans d.action_le
  have hp := position_map (realizes_position hA hle) d.quotientEquiv.symm
  rw [← d.image_eq A] at hp
  have hid : d.quotientEquiv.symm.toMonoidHom.comp d.quotientEquiv.toMonoidHom = MonoidHom.id H := by
    ext x
    exact d.quotientEquiv.symm_apply_apply x
  rw [map_map, hid, map_id] at hp
  exact hp

private theorem quotientMap_mem_even (x : SylowGroup) :
    quotientMap x ∈ evenFour ↔ x.val ∈ alternatingGroup (Fin 8) := by
  have hk : quotientMap.ker ≤ evenSylow := by
    rw [quotientMap, QuotientGroup.ker_mk']
    exact sylowCore_le_evenSylow
  have he : evenFour.comap quotientMap = evenSylow := comap_map_eq_self hk
  exact SetLike.ext_iff.mp he x

/-- The marking is determined by the actual action parity, not by a supplied
 identification of the two four-groups. -/
theorem mem_marked (d : LocalCoordinates f q) (s : G) :
    q s ∈ d.marked ↔ f s ∈ alternatingGroup (Fin 8) := by
  change q s ∈ evenFour.map d.quotientEquiv.symm.toMonoidHom ↔ _
  rw [mem_map_equiv]
  change d.quotientEquiv (q s) ∈ evenFour ↔ _
  rw [d.compatible]
  exact quotientMap_mem_even _

/-- Compatible actor and quotient conjugations, together with a permutation
 relabeling between the two actions, determine the second marked four-group. -/
theorem marked_conjugate (d : LocalCoordinates f q) (e : LocalCoordinates g q)
    (hq : Function.Surjective q) (σ : MulAut G) (α : MulAut H)
    (hquot : ∀ s, q (σ s) = α (q s)) (r : Perm)
    (hact : ∀ s, g (σ s) = r * f s * r⁻¹) :
    d.marked.map α.toMonoidHom = e.marked := by
  ext z
  obtain ⟨x, rfl⟩ := α.surjective z
  rw [mem_map_equiv, α.symm_apply_apply]
  obtain ⟨s, rfl⟩ := hq x
  rw [← hquot, d.mem_marked, e.mem_marked, hact]
  change Equiv.Perm.sign (f s) = 1 ↔ Equiv.Perm.sign (r * f s * r⁻¹) = 1
  rw [map_mul, map_mul, map_inv]
  constructor
  · intro h
    rw [h, mul_one, mul_inv_cancel]
  · intro h
    have hh := congrArg (fun z => (Equiv.Perm.sign r)⁻¹ * z * Equiv.Perm.sign r) h
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one, one_mul] using hh

/-- Two actual action diagrams give the source SD16 pairings. All comparisons
 of marks and cases are conclusions of the compatible action equations. -/
theorem cases_of_semidihedral (d : LocalCoordinates f q) (e : LocalCoordinates g q)
    (hq : Function.Surjective q) (σ : MulAut G) (α : MulAut H)
    (hquot : ∀ s, q (σ s) = α (q s)) (r : Perm)
    (hact : ∀ s, g (σ s) = r * f s * r⁻¹)
    (v : K ≃* SD16) (j : H →* K) (hj : Function.Injective j)
    (t : K) (ht : t ∉ j.range) (hconj : ∀ x, j (α x) = t * j x * t⁻¹)
    {A : Subgroup G} {c c' : EightCase}
    (hA : c.Realizes (A.map f)) (hA' : c'.Realizes (A.map g)) :
    (c = .regular ∧ c' = .transposition) ∨
    (c = .transposition ∧ c' = .regular) ∨ (c = .even ∧ c' = .even) := by
  have hp := e.position_of_realizes hA'
  rw [← d.marked_conjugate e hq σ α hquot r hact] at hp
  exact positions_of_semidihedral_conjugation (d.quotientEquiv.trans dihedralEquiv)
    v j hj t ht α hconj (d.card_marked) (d.position_of_realizes hA) hp

/-- If the quotient conjugator belongs to the local quotient, its induced
 automorphism is inner and preserves the actual four-group marking. -/
theorem marked_fixed_of_inner (d : LocalCoordinates f q)
    (j : H →* K) (hj : Function.Injective j) (t : K) (ht : t ∈ j.range)
    (α : MulAut H) (hconj : ∀ x, j (α x) = t * j x * t⁻¹) :
    d.marked.map α.toMonoidHom = d.marked := by
  obtain ⟨w, rfl⟩ := ht
  have he : α = MulAut.conj w := by
    ext x
    apply hj
    simpa only [MulAut.conj_apply, map_mul, map_inv] using hconj x
  rw [he]
  exact dihedral_four_conj (d.quotientEquiv.trans dihedralEquiv) d.marked d.card_marked w

/-- Equal quotient images put the quotient conjugator inside the D8 image;
 the two actual actions consequently have the same case. -/
theorem cases_of_inner (d : LocalCoordinates f q) (e : LocalCoordinates g q)
    (hq : Function.Surjective q) (σ : MulAut G) (α : MulAut H)
    (hquot : ∀ s, q (σ s) = α (q s)) (r : Perm)
    (hact : ∀ s, g (σ s) = r * f s * r⁻¹)
    (j : H →* K) (hj : Function.Injective j) (t : K) (ht : t ∈ j.range)
    (hconj : ∀ x, j (α x) = t * j x * t⁻¹)
    {A : Subgroup G} {c c' : EightCase}
    (hA : c.Realizes (A.map f)) (hA' : c'.Realizes (A.map g)) : c = c' := by
  have hm := d.marked_conjugate e hq σ α hquot r hact
  rw [d.marked_fixed_of_inner j hj t ht α hconj] at hm
  have hp := e.position_of_realizes hA'
  rw [← hm] at hp
  apply Position.unique (d.position_of_realizes hA) hp
  · exact (Nat.card_congr (centerCongr d.quotientEquiv).toEquiv).trans card_center
  · exact d.center_le_marked

end LocalCoordinates

/-- Existing Sylow diagrams restrict to local actors, so no extension of either
 permutation action to the module-swapping overgroup is introduced. -/
def localCoordinates {S : Subgroup G} {f : G →* Perm} {q : G →* H}
    (d : SylowCoordinates S f q) :
    LocalCoordinates (f.comp S.subtype) (q.subgroupMap S) where
  action_le := by
    rintro x ⟨s, rfl⟩
    exact d.action_le (mem_map_of_mem f s.property)
  quotientEquiv := d.quotientEquiv
  compatible := d.compatible

/-- The equal-image branch for the original quotient map. The actor
 conjugation is defined only on S, and its quotient compatibility is proved
 from the two displayed conjugation equations. -/
theorem cases_of_equal_quotient_images
    (S T : Subgroup G) (q : G →* H) (f g : S →* Perm)
    (d : LocalCoordinates f (q.subgroupMap S))
    (e : LocalCoordinates g (q.subgroupMap S))
    (he : S.map q = T.map q) (t : G) (ht : t ∈ T)
    (σ : MulAut S) (hσ : ∀ s : S, (σ s : G) = t * s * t⁻¹)
    (α : MulAut (S.map q))
    (hα : ∀ x : S.map q, (α x : H) = q t * x * (q t)⁻¹)
    (r : Perm) (hact : ∀ s, g (σ s) = r * f s * r⁻¹)
    {A : Subgroup S} {c c' : EightCase}
    (hA : c.Realizes (A.map f)) (hA' : c'.Realizes (A.map g)) : c = c' := by
  have htq : q t ∈ (S.map q).subtype.range := by
    refine ⟨⟨q t, ?_⟩, rfl⟩
    rw [he]
    exact mem_map_of_mem q ht
  have hquot : ∀ s : S, q.subgroupMap S (σ s) = α (q.subgroupMap S s) := by
    intro s
    apply Subtype.ext
    change q (σ s : G) = (α (q.subgroupMap S s) : H)
    rw [hα, hσ, map_mul, map_mul, map_inv]
    rfl
  exact d.cases_of_inner e (q.subgroupMap_surjective S) σ α hquot r hact
    (S.map q).subtype (S.map q).subtype_injective (q t) htq hα hA hA'

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient.Conjugation

end
