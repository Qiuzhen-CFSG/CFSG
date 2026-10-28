module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeEven.TorusParity
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.TorusSplitting

/-!
# The marked torus in an arbitrary faithful linear completion

The native diagonal torus is Hall in the whole embedded Borel and has trivial
normalizer intersection with the embedded unipotent subgroup. Its normalizer
inside either embedded parabolic consists of the two exact reflection cosets.
Consequently the same endpoint reflections normalize the enlarged torus
stabilizer in any common normalizer preserving the original local markings.
No ambient recognition or identification of the common normalizer with the
native Borel is used. Source: Aschbacher–Smith F.4.49, printed pp.298–299,
`refs/quasithin.pdf`, with the projective scalar kernel retained at q=4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3.SmallCompletion
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven.NativeCompletion
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {G : Type*} [Group G] (c : NativeCompletion F G)

omit [CharP F 2] in
theorem torus_range_map : c.torusHom.range =
    ((torus F).subgroupOf (borel F)).map c.middle := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨⟨torusMap F a,torus_le_borel F ⟨a,rfl⟩⟩,⟨a,rfl⟩,rfl⟩
  · rintro ⟨b,⟨a,ha⟩,rfl⟩
    exact ⟨a,congrArg c.middle (Subtype.ext ha)⟩

omit [CharP F 2] in
theorem torus_le_middle : c.torusHom.range ≤ c.middle.range := by
  rintro x ⟨a,rfl⟩
  exact ⟨_,rfl⟩

omit [CharP F 2] in
theorem torus_hall {n : ℕ} (hF : Nat.card F=2^n) :
    IsHallSubgroup Subgroup.OddHall.oddPrimes
      (c.torusHom.range.subgroupOf c.middle.range) := by
  let e := MonoidHom.ofInjective c.middle_injective
  have hm : ((torus F).subgroupOf (borel F)).map e.toMonoidHom =
      c.torusHom.range.subgroupOf c.middle.range := by
    apply Subgroup.map_injective c.middle.range.subtype_injective
    rw [map_subgroupOf_eq_of_le c.torus_le_middle,Subgroup.map_map]
    exact c.torus_range_map.symm
  rw [←hm]
  constructor
  · intro p hp
    apply (LinearAmbientGeometry.torus_oddHall F hF).p_in_pi_of_p_dvd_card p
    exact (card_map_of_injective (K := (torus F).subgroupOf (borel F))
      (f := e.toMonoidHom) e.injective) ▸ hp
  · intro p hp
    apply (LinearAmbientGeometry.torus_oddHall F hF).p_in_pi_of_p_dvd_index p
    exact (index_map_equiv (H := (torus F).subgroupOf (borel F)) e) ▸ hp

omit [CharP F 2] in
theorem unipotent_torus_disjoint {n : ℕ} (hF : Nat.card F=2^n)
    (hq : 2<Nat.card F) :
    Disjoint (((unipotent F).subgroupOf (borel F)).map c.middle)
      (normalizer (c.torusHom.range : Set G)) := by
  apply disjoint_def.mpr
  rintro x ⟨u,hu,rfl⟩ hn
  have hnu : u ∈ normalizer ((torus F).subgroupOf (borel F) : Set (borel F)) := by
    rw [mem_normalizer_iff]
    intro v
    have hmem (a : borel F) : c.middle a ∈ c.torusHom.range ↔ a ∈ (torus F).subgroupOf (borel F) := by
      rw [c.torus_range_map]
      exact mem_map_iff_mem c.middle_injective
    simpa only [←map_inv,←map_mul,hmem] using
      (mem_normalizer_iff.mp hn (c.middle v))
  have hnt := ((torus F).subgroupOf (borel F)).le_normalizer_map
    (borel F).subtype (mem_map_of_mem _ hnu)
  rw [map_subgroupOf_eq_of_le (torus_le_borel F)] at hnt
  have he := LinearAmbientGeometry.unipotent_torus_normalizer_trivial F hF hq u.val hu hnt
  rw [show u=1 from Subtype.ext he,map_one]

theorem endpoint_torus_normalizer
    (hq : 2<Nat.card F) (i : Bool) (x : G) (hx : x ∈ c.family i)
    (hn : x ∈ normalizer (c.torusHom.range : Set G)) :
    x ∈ c.torusHom.range ∨ x*c.weyl i ∈ c.torusHom.range := by
  have hr : (c.endpointHom i).range=c.family i := by cases i <;> rfl
  obtain ⟨a,rfl⟩ := hr.symm ▸ hx
  have han : a.val ∈ normalizer (torus F : Set PSL(3,F)) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨e,rfl⟩
      have hh := (mem_normalizer_iff.mp hn (c.torusHom e)).mp ⟨e,rfl⟩
      obtain ⟨f,hf⟩ := hh
      rw [←c.endpointHom_torus i e,←map_inv,←map_mul,←map_mul,
        ←c.endpointHom_torus i f] at hf
      exact ⟨f,congrArg Subtype.val (c.endpointHom_injective i hf)⟩
    · intro hy
      have hh : a.val⁻¹*(a.val*y*a.val⁻¹)*a.val=y := by group
      have hyp : y ∈ parabolic F i := by
        rw [←hh]
        exact (parabolic F i).mul_mem
          ((parabolic F i).mul_mem ((parabolic F i).inv_mem a.property)
            ((torus_le_borel F).trans (borel_le_parabolic F i) hy)) a.property
      let b : parabolic F i := ⟨y,hyp⟩
      obtain ⟨e,he⟩ := hy
      have he' : c.torusHom e = c.endpointHom i a * c.endpointHom i b * (c.endpointHom i a)⁻¹ := by
        rw [←c.endpointHom_torus i e,←map_inv,←map_mul,←map_mul]
        exact congrArg (c.endpointHom i) (Subtype.ext he)
      have hb : c.endpointHom i b ∈ c.torusHom.range :=
        (mem_normalizer_iff.mp hn _).mpr ⟨e,he'⟩
      obtain ⟨f,hf⟩ := hb
      rw [←c.endpointHom_torus i f] at hf
      exact ⟨f,congrArg Subtype.val (c.endpointHom_injective i hf)⟩
  obtain ⟨u,hu⟩ := projection_surjective F a.val
  have hup : u ∈ parabolicSL F i := by
    have ha := hu ▸ a.property
    cases i
    · change u ∈ (pointParabolic F).comap (projection F) at ha
      rwa [pointParabolic_comap] at ha
    · change u ∈ (lineParabolic F).comap (projection F) at ha
      rwa [lineParabolic_comap] at ha
  rcases normalizerSL_two_cosets F hq i u hup (hu ▸ han) with ⟨e,he⟩ | ⟨e,he⟩
  · left
    refine ⟨e,?_⟩
    rw [←c.endpointHom_torus i e]
    apply congrArg (c.endpointHom i)
    exact Subtype.ext ((congrArg (projection F) he).trans hu)
  · right
    refine ⟨e,?_⟩
    rw [←c.endpointHom_torus i e,weyl,←map_mul]
    apply congrArg (c.endpointHom i)
    apply Subtype.ext
    exact (congrArg (projection F) he).trans (by rw [map_mul,hu]; rfl)


theorem middle_torus_normalizer_eq (hq : 2<Nat.card F) :
    c.middle.range ⊓ normalizer (c.torusHom.range : Set G)=c.torusHom.range := by
  apply le_antisymm _ (le_inf c.torus_le_middle c.torusHom.range.le_normalizer)
  rintro x ⟨hx,hn⟩
  rcases c.endpoint_torus_normalizer hq false x (c.middle_le_left hx) hn with hd | hd
  · exact hd
  · have hh := c.middle.range.mul_mem (c.middle.range.inv_mem hx) (c.torus_le_middle hd)
    exact (c.weyl_not_mem_middle false (by simpa only [inv_mul_cancel_left] using hh)).elim

/-- A common normalizer preserving both local markings also carries their
specified reflections into the normalizer of the same enlarged torus stabilizer. -/
theorem weyl_normalizes_full_torus_stabilizer (hq : 2<Nat.card F)
    (N : Subgroup G) (hCN : c.middle.range≤N)
    (hNP : ∀ i, N≤normalizer (c.family i : Set G))
    (hNC : N≤normalizer (c.middle.range : Set G)) (i : Bool) :
    c.weyl i ∈ normalizer ((N ⊓ normalizer (c.torusHom.range : Set G) : Subgroup G) : Set G) := by
  let B := N ⊓ normalizer (c.torusHom.range : Set G)
  let s := c.weyl i
  have hs : s⁻¹=s := inv_eq_of_mul_eq_one_right (by simpa only [←pow_two] using c.weyl_sq i)
  have hconj (b : G) (hb : b∈B) : s*b*s⁻¹∈B := by
    have hbN : b⁻¹∈N := N.inv_mem hb.1
    have hbD : b⁻¹∈normalizer (c.torusHom.range : Set G) := (normalizer _).inv_mem hb.2
    have hxP : b⁻¹*s*b ∈ c.family i := by
      simpa only [inv_inv] using (mem_normalizer_iff.mp (hNP i hbN) s).mp (c.weyl_mem i)
    have hxD : b⁻¹*s*b ∈ normalizer (c.torusHom.range : Set G) :=
      (normalizer _).mul_mem ((normalizer _).mul_mem hbD (c.weyl_normalizes_torus i)) hb.2
    have hout : b⁻¹*s*b ∉ c.middle.range := by
      intro hh
      apply c.weyl_not_mem_middle i
      exact (mem_normalizer_iff.mp (hNC hbN) s).mpr (by simpa only [inv_inv] using hh)
    have hx := c.endpoint_torus_normalizer hq i _ hxP hxD
    have hx' : b⁻¹*s*b*s ∈ c.torusHom.range :=
      hx.resolve_left (fun hd => hout (c.torus_le_middle hd))
    refine ⟨?_,(normalizer _).mul_mem
      ((normalizer _).mul_mem (c.weyl_normalizes_torus i) hb.2)
      ((normalizer _).inv_mem (c.weyl_normalizes_torus i))⟩
    change s*b*s⁻¹ ∈ N
    rw [hs]
    have hh := N.mul_mem hb.1 (hCN (c.torus_le_middle hx'))
    simpa only [←mul_assoc,mul_inv_cancel,mul_one,one_mul] using hh
  rw [mem_normalizer_iff]
  intro b
  refine ⟨hconj b,fun hb => ?_⟩
  have hh := hconj _ hb
  have he : s*(s*b*s⁻¹)*s⁻¹=b := by
    rw [hs]
    have hss : s*s=1 := by simpa only [←pow_two] using c.weyl_sq i
    calc
      _ = (s*s)*b*(s*s) := by group
      _ = b := by rw [hss,one_mul,mul_one]
  exact he ▸ hh

end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven.NativeCompletion
