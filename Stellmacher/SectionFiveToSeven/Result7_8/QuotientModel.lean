module

public import Stellmacher.SectionFiveToSeven.Defs
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The quotient product model for the local dihedral configuration

The internal product in the image of `L` in `P/O₂(P)` determines the
`QuotientDihedralProduct` used by (7.8). Multiplication of the commuting,
disjoint factors gives the product equivalence. The map on `L` is the
actual restriction of the quotient map; its kernel and the central actor
image are verified explicitly. Source: Stellmacher (7.8)(b), p. 36.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

public theorem quotientDihedralProduct_of_internal_image
    {G : Type*} [Group G] [Finite G]
    (P L A₀ : Subgroup G) (hLP : L ≤ P) (hA₀L : A₀ ≤ L)
    (p n : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (E : Subgroup (P ⧸ pCore 2 P))
    (hE : Nonempty (E ≃* DihedralGroup (p ^ n)))
    (hprod : IsInternalDirectProductFamily
      ((L.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)))
      (fun i : Bool => if i then E else
        (A₀.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)))) :
    Nonempty (QuotientDihedralProduct L (twoCoreAmbient P) A₀) := by
  classical
  let q := QuotientGroup.mk' (pCore 2 P)
  let J := (L.subgroupOf P).map q
  let C := (A₀.subgroupOf P).map q
  have hCJ : C ≤ J := Subgroup.map_mono (Subgroup.subgroupOf_mono P hA₀L)
  let Cj := C.subgroupOf J
  let f₀ : L →* P ⧸ pCore 2 P := q.comp (Subgroup.inclusion hLP)
  let f : L →* J := f₀.codRestrict J (fun l => Subgroup.mem_map_of_mem q l.property)
  have hf : Function.Surjective f := by
    intro j
    obtain ⟨l, hl, hlj⟩ := j.property
    exact ⟨⟨(l : G), hl⟩, Subtype.ext hlj⟩
  have hker : f.ker = (L ⊓ twoCoreAmbient P).subgroupOf L := by
    ext l
    constructor
    · intro hl
      refine ⟨l.property, ?_⟩
      have hq : q (Subgroup.inclusion hLP l) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
      exact Subgroup.mem_map_of_mem P.subtype
        ((QuotientGroup.eq_one_iff (Subgroup.inclusion hLP l)).mp hq)
    · rintro ⟨_, b, hb, hbl⟩
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      change q (Subgroup.inclusion hLP l) = 1
      have heq : b = Subgroup.inclusion hLP l := Subtype.ext hbl
      rw [← heq]
      exact (QuotientGroup.eq_one_iff b).mpr hb
  have hCimage : Cj = (⊤ : Subgroup A₀).map
      (f.comp (Subgroup.inclusion hA₀L)) := by
    ext j
    constructor
    · intro hj
      obtain ⟨b, hb, hbj⟩ := hj
      exact ⟨⟨(b : G), hb⟩, trivial, Subtype.ext hbj⟩
    · rintro ⟨b, _, rfl⟩
      exact Subgroup.mem_map_of_mem q b.property
  have hJE : J = E ⊔ C := by
    simpa only [iSup_bool_eq, Bool.false_eq_true, ite_false, ite_true] using hprod.1
  have hdis : Disjoint E C := hprod.2.1 true false (by decide)
  have hcomm : ∀ e : E, ∀ c : C, Commute (e : P ⧸ pCore 2 P) (c : P ⧸ pCore 2 P) := by
    intro e c
    exact hprod.2.2 true false (by decide) e e.property c c.property
  let m : E × C →* P ⧸ pCore 2 P := E.subtype.noncommCoprod C.subtype hcomm
  have hminj : Function.Injective m := by
    apply (MonoidHom.noncommCoprod_injective E.subtype C.subtype hcomm).mpr
    exact ⟨E.subtype_injective, C.subtype_injective,
      by simpa only [Subgroup.range_subtype] using hdis⟩
  have hmrange : m.range = J := by
    calc
      m.range = E.subtype.range ⊔ C.subtype.range :=
        MonoidHom.noncommCoprod_range E.subtype C.subtype hcomm
      _ = E ⊔ C := by rw [Subgroup.range_subtype, Subgroup.range_subtype]
      _ = J := hJE.symm
  let em : E × C ≃* m.range := MulEquiv.ofBijective m.rangeRestrict
    ⟨fun _ _ h => hminj (congrArg Subtype.val h), m.rangeRestrict_surjective⟩
  let eprod : E × C ≃* J := em.trans (MulEquiv.subgroupCongr hmrange)
  let eC : Cj ≃* C := Subgroup.subgroupOfEquivOfLe hCJ
  obtain ⟨eE⟩ := hE
  let eModel : J ≃* (DihedralGroup (p ^ n) × Cj) :=
    eprod.symm.trans (MulEquiv.prodCongr eE eC.symm)
  exact ⟨{
    A0_le_L := hA₀L
    p := p
    n := n
    p_prime := hp
    p_odd := hpodd
    barL := J
    barA0 := Cj
    quotientMap := f
    quotient_surjective := hf
    quotient_kernel := hker
    barA0_image := hCimage
    model := ⟨eModel⟩ }⟩

end Stellmacher.SectionsFiveToSeven
