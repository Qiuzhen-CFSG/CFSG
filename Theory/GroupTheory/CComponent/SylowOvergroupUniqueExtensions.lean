module
public import Theory.GroupTheory.CComponent.SylowOvergroupUnique
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Solvable extensions and parabolic restrictions

A solvable quotient forces every perfect subgroup into its kernel. Intersecting
an ambient Sylow with that normal kernel supplies the full intrinsic Sylow,
so uniqueness of C-components passes from the kernel to the whole group.
Restriction to a containing subgroup handles the parabolic placement step.
These are the extension arguments used in Aschbacher--Smith A.3.12, pp.47--48.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SylowOvergroupComponentUnique
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Restrict a full ambient Sylow to a containing subgroup with uniqueness. -/
theorem eq_of_le_overgroup (S : Sylow 2 G) {P J : Subgroup G}
    (hSP : (S : Subgroup G) ≤ P) (hPJ : P ≤ J)
    (hJ : SylowOvergroupComponentUnique J)
    {B C : Subgroup P} (hB : B.IsCComponent) (hC : C.IsCComponent) : B = C := by
  let e : P ≃* P.subgroupOf J := (subgroupOfEquivOfLe hPJ).symm
  apply map_injective (f := e.toMonoidHom) e.injective
  exact hJ (S.subtype (hSP.trans hPJ)) (P.subgroupOf J)
    (fun _ hx => hSP hx) _ _ (hB.map_equiv e) (hC.map_equiv e)

/-- Uniqueness passes through a solvable extension of a normal subgroup. -/
theorem of_solvable_quotient (N : Subgroup G) [N.Normal]
    [Group.IsSolvable (G ⧸ N)] (hN : SylowOvergroupComponentUnique N) :
    SylowOvergroupComponentUnique G := by
  intro S P hSP B C hB hC
  let R := N.comap P.subtype
  have hBR : B ≤ R := by
    let := hB.perfect
    let : Group.IsPerfect (B.map P.subtype) := Group.IsPerfect.ofSurjective
      (f := P.subtype.subgroupMap B) (P.subtype.subgroupMap_surjective B)
    have h := le_of_isPerfect_of_solvable_quotient (B.map P.subtype) N
    exact fun b hb => h (mem_map_of_mem P.subtype hb)
  have hCR : C ≤ R := by
    let := hC.perfect
    let : Group.IsPerfect (C.map P.subtype) := Group.IsPerfect.ofSurjective
      (f := P.subtype.subgroupMap C) (P.subtype.subgroupMap_surjective C)
    have h := le_of_isPerfect_of_solvable_quotient (C.map P.subtype) N
    exact fun c hc => h (mem_map_of_mem P.subtype hc)
  let e : R ≃* P.subgroupOf N :=
    { toFun := fun x => ⟨⟨x.val.val,x.property⟩,x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val,x.property⟩,x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  obtain ⟨T,hT⟩ := S.exists_subgroupOf_eq_of_normal N
  have hTP : (T : Subgroup N) ≤ P.subgroupOf N := by
    rw [hT]
    exact fun _ hx => hSP hx
  have he := hN T (P.subgroupOf N) hTP _ _
    ((hB.subgroupOf hBR).map_equiv e) ((hC.subgroupOf hCR).map_equiv e)
  have hh := (map_injective (f := e.toMonoidHom) e.injective) he
  have := congrArg (Subgroup.map R.subtype) hh
  simpa only [map_subgroupOf_eq_of_le hBR, map_subgroupOf_eq_of_le hCR] using this
omit [Finite G] in
/-- A solvable group has no C-components, hence satisfies uniqueness. -/
theorem of_isSolvable [Group.IsSolvable G] : SylowOvergroupComponentUnique G := by
  intro S P hSP B C hB hC
  exact (hB.not_isSolvable inferInstance).elim

/-- A solvable normal kernel can be removed before calculating uniqueness. -/
theorem of_quotient (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (h : SylowOvergroupComponentUnique (G ⧸ N)) : SylowOvergroupComponentUnique G := by
  let : Group.IsSolvable (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  exact of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) h

/-- A concrete description of a parabolic residual suffices for uniqueness. -/
theorem of_residual_image {H : Type*} [Group H] (P N : Subgroup H)
    [Finite P] (he : (solvableResidual P).map P.subtype = N)
    (h : SylowOvergroupComponentUnique N) : SylowOvergroupComponentUnique P := by
  apply of_solvable_quotient (solvableResidual P)
  exact of_equiv
    (((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr he)) h

/-- Exhaustive placement into conjugate parabolics reduces the simple case
to the intrinsic uniqueness calculations in those parabolics. -/
theorem of_proper_conjugate_cover [IsSimpleGroup G] [Group.IsPerfect G]
    (h : ∀ (S : Sylow 2 G) (P : Subgroup G), (S : Subgroup G) ≤ P → P ≠ ⊤ →
      ∃ (g : G) (J : Subgroup G), P.map (MulAut.conj g).toMonoidHom ≤ J ∧
        SylowOvergroupComponentUnique J) : SylowOvergroupComponentUnique G := by
  apply of_proper_overgroups
  intro S P hSP hP B C hB hC
  obtain ⟨g,J,hPJ,hJ⟩ := h S P hSP hP
  let e := (MulAut.conj g).subgroupMap P
  apply map_injective (f := e.toMonoidHom) e.injective
  exact eq_of_le_overgroup (S.mapSurjective (MulAut.conj g).surjective)
    (map_mono hSP) hPJ hJ (hB.map_equiv e) (hC.map_equiv e)

end Theory.GroupTheory.SylowOvergroupComponentUnique

namespace Theory.GroupTheory.SylowOvergroupComponentUnique
variable {G H : Type*} [Group G] [Group H]
/-- A solvable direct factor contributes no C-components. -/
theorem prod_right [Finite G] [Finite H] [Group.IsSolvable H]
    (h : SylowOvergroupComponentUnique G) : SylowOvergroupComponentUnique (G × H) := by
  let f := MonoidHom.fst G H
  let g : f.ker →* H := (MonoidHom.snd G H).comp f.ker.subtype
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective (f := g) (by
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · exact x.property.trans y.property.symm
    · exact hxy)
  exact of_surjective f (fun x => ⟨(x,1),rfl⟩) h

/-- The same statement with the solvable factor first. -/
theorem prod_left [Finite G] [Finite H] [Group.IsSolvable G]
    (h : SylowOvergroupComponentUnique H) : SylowOvergroupComponentUnique (G × H) :=
  of_equiv MulEquiv.prodComm (prod_right h)

/-- Lift from a relatively normal subgroup with a solvable supplement. -/
theorem of_solvable_supplement (L B P : Subgroup G) [Finite P]
    (hL : L ≤ P) (hB : B ≤ P) [(L.subgroupOf P).Normal] [Group.IsSolvable B]
    (hgen : L ⊔ B = P) (h : SylowOvergroupComponentUnique L) :
    SylowOvergroupComponentUnique P := by
  have hg : L.subgroupOf P ⊔ B.subgroupOf P = ⊤ := by
    rw [← subgroupOf_sup hL hB, hgen, subgroupOf_self]
  let q := QuotientGroup.mk' (L.subgroupOf P)
  let f : B.subgroupOf P →* P ⧸ L.subgroupOf P := q.comp (B.subgroupOf P).subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf P) y
    obtain ⟨l,hl,b,hb,rfl⟩ := mem_sup_of_normal_left.mp (hg.symm ▸ mem_top x)
    refine ⟨⟨b,hb⟩,?_⟩
    change q b = q (l*b)
    rw [map_mul, show q l = 1 from (QuotientGroup.eq_one_iff l).mpr hl, one_mul]
  let : Group.IsSolvable (B.subgroupOf P) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hB).toMonoidHom) (subgroupOfEquivOfLe hB).injective
  let : Group.IsSolvable (P ⧸ L.subgroupOf P) := Group.isSolvable_of_surjective hf
  apply of_solvable_quotient (L.subgroupOf P)
  exact of_equiv (subgroupOfEquivOfLe hL) h

end Theory.GroupTheory.SylowOvergroupComponentUnique
