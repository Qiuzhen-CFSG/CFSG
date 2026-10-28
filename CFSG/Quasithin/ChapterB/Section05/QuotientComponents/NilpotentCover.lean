module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.Fitting.Core
public import Theory.Quasithin.Rank
public import Mathlib.Order.Minimal

/-!
# Nilpotent SQTK covers

This proves assertions (1) and (2) of Aschbacher--Smith, *The Classification
of Quasithin Groups*, Lemma B.5.2, printed p.103 of the combined 1 March 2004
manuscript. The input is an actual surjection from a finite SQTK group.
The output retains that group-class parameter and supplies a new finite SQTK
cover with nilpotent Fitting preimage and nilpotent kernel of odd order.
Its literal quotient by the kernel is identified with the target compatibly
with the covering map.

Choose an inclusion-minimal subgroup of the original cover still mapping onto
the target. For a Sylow subgroup of a nilpotent normal preimage, its image is
normal. Apply the Frattini argument inside the preimage of this image; its
normalizer still surjects, so minimality makes the Sylow subgroup normal in
the whole cover. Thus the Fitting preimage is nilpotent. Quotient by the
kernel's characteristic Sylow two-subgroup. The remaining kernel has odd
order, and odd-prime rank does not increase under this two-group quotient.

The final consequence identifies the ambient image of every Sylow three-
subgroup of the three-core preimage: it is normal and maps onto the three-core.
The same fact is proved for every prime in `sylow_pCore_preimage`.
-/

open Subgroup

namespace CFSG.Quasithin.ChapterB.NilpotentCover

variable {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]

-- The Frattini argument is applied to the preimage of the Sylow image,
-- rather than to the entire nilpotent preimage: this gives a supplement
-- modulo the kernel, which is what the minimality hypothesis requires.
private theorem normal_sylow_preimage (f : H →* G) (hf : Function.Surjective f)
    (hmin : ∀ U : Subgroup H, U.map f = ⊤ → U = ⊤)
    (N : Subgroup G) [N.Normal] [Group.IsNilpotent N]
    (p : ℕ) [Fact p.Prime] (P : Sylow p (N.comap f)) :
    (P.map (N.comap f).subtype).Normal := by
  let A := N.comap f
  let q : A →* N := f.subgroupComap N
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective N hf
  let R : Subgroup H := P.map A.subtype
  have hRN : R ≤ A := map_subtype_le _
  have himage : R.map f = (P.map q).map N.subtype := by
    rw [map_map, map_map]
    rfl
  have hnimage : (R.map f).Normal := by
    rw [himage]
    exact Sylow.normal_of_nilpotent_normal (inferInstance : N.Normal)
      (inferInstance : Group.IsNilpotent N) p (P.mapSurjective hq)
  let M : Subgroup H := (R.map f).comap f
  have hM : M = R ⊔ f.ker := comap_map_eq f R
  have hRM : R ≤ M := hM ▸ le_sup_left
  have hMA : M ≤ A := by
    rw [hM]
    refine sup_le hRN ?_
    intro x hx
    change f x ∈ N
    rw [MonoidHom.mem_ker.mp hx]
    exact N.one_mem
  let : M.Normal := @Subgroup.normal_comap _ _ _ _ (R.map f) hnimage f
  have hRidx : ¬ p ∣ (R.subgroupOf M).index := by
    have hd : R.relIndex M ∣ R.relIndex A := by
      rw [← relIndex_mul_relIndex R M A hRM hMA]
      exact dvd_mul_right _ _
    have he : R.relIndex A = (P : Subgroup A).index := by
      change ((P : Subgroup A).map A.subtype |>.comap A.subtype).index = _
      rw [comap_map_eq_self_of_injective A.subtype_injective]
    exact fun h => P.not_dvd_index (he ▸ h.trans hd)
  let S : Sylow p M := ((P.isPGroup'.map A.subtype).comap_subtype).toSylow hRidx
  have hSR : S.map M.subtype = R := by
    change (R.subgroupOf M).map M.subtype = R
    exact map_subgroupOf_eq_of_le hRM
  have hfr := S.normalizer_sup_eq_top
  rw [hSR, hM, ← sup_assoc, sup_of_le_left R.le_normalizer] at hfr
  have hsurj : (normalizer (R : Set H)).map f = ⊤ := by
    have he := congrArg (Subgroup.map f) hfr
    simpa only [Subgroup.map_sup, Subgroup.map_ker_self, sup_bot_eq,
      map_top_of_surjective f hf] using he
  exact normalizer_eq_top_iff.mp (hmin _ hsurj)

private theorem nilpotent_preimage (f : H →* G) (hf : Function.Surjective f)
    (hmin : ∀ U : Subgroup H, U.map f = ⊤ → U = ⊤)
    (N : Subgroup G) [N.Normal] [Group.IsNilpotent N] :
    Group.IsNilpotent (N.comap f) := by
  apply (Group.isNilpotent_of_finite_tfae.out 0 3 rfl rfl).mpr
  intro p hp P
  exact (normal_sylow_preimage f hf hmin N p P).of_map_subtype

omit [Finite G] in
private theorem exists_minimal_surjection (f : H →* G) (hf : Function.Surjective f) :
    ∃ U : Subgroup H, Function.Surjective (f.comp U.subtype) ∧
      ∀ V : Subgroup U, V.map (f.comp U.subtype) = ⊤ → V = ⊤ := by
  obtain ⟨U, hU, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun U : Subgroup H => U.map f = ⊤) ⟨⊤, map_top_of_surjective f hf⟩
  refine ⟨U, ?_, ?_⟩
  · intro g
    obtain ⟨h, hh, he⟩ := (show g ∈ U.map f from hU.symm ▸ mem_top g)
    exact ⟨⟨h, hh⟩, he⟩
  · intro V hV
    have hle : U ≤ V.map U.subtype :=
      hmin (by simpa only [map_map] using hV) (map_subtype_le V)
    apply map_injective U.subtype_injective
    rw [← MonoidHom.range_eq_map, U.range_subtype]
    exact le_antisymm (map_subtype_le V) hle

omit [Finite H] in
private theorem nilpotent_of_le {A B : Subgroup H} [Group.IsNilpotent B]
    (h : A ≤ B) : Group.IsNilpotent A :=
  Group.nilpotent_of_mulEquiv (subgroupOfEquivOfLe h)

-- Taking a quotient within the kernel preserves the nilpotent preimages.
omit [Finite H] [Finite G] in
private theorem nilpotent_preimage_lift (f : H →* G) (D : Subgroup H) [D.Normal]
    (hD : D ≤ f.ker) (N : Subgroup G) [Group.IsNilpotent (N.comap f)] :
    Group.IsNilpotent (N.comap (QuotientGroup.lift D f hD)) := by
  let q := QuotientGroup.mk' D
  let g := QuotientGroup.lift D f hD
  have he : (N.comap g).comap q = N.comap f := by
    rw [comap_comap, QuotientGroup.lift_comp_mk']
  have hm : (N.comap f).map q = N.comap g := by
    rw [← he, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective D)]
  have : Group.IsNilpotent ((N.comap f).map q) :=
    Group.nilpotent_of_surjective (q.subgroupMap (N.comap f))
      (q.subgroupMap_surjective (N.comap f))
  rwa [hm] at this

/-- If the Fitting preimage of a finite surjection is nilpotent, every Sylow
subgroup of the corresponding prime-core preimage is normal in the cover,
and its ambient image maps onto the whole prime core. In particular `p = 3`
is the normal-three-preimage consequence used in F.6.9. -/
public theorem sylow_pCore_preimage (f : H →* G) (hf : Function.Surjective f)
    [Group.IsNilpotent ((fittingSubgroup G).comap f)]
    (p : ℕ) [Fact p.Prime] (P : Sylow p ((pCore p G).comap f)) :
    (P.map ((pCore p G).comap f).subtype).Normal ∧
      (P.map ((pCore p G).comap f).subtype).map f = pCore p G := by
  let A := (pCore p G).comap f
  have : Group.IsNilpotent A := nilpotent_of_le (comap_mono (pCore_le_fitting G p))
  refine ⟨Sylow.normal_of_nilpotent_normal inferInstance this p P, ?_⟩
  let q : A →* pCore p G := f.subgroupComap (pCore p G)
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective _ hf
  have he : (P.mapSurjective hq : Subgroup (pCore p G)) = ⊤ :=
    ((P.mapSurjective hq).is_maximal' (pCore_isPGroup.to_subgroup ⊤) le_top).symm
  calc
    (P.map A.subtype).map f = (P.map q).map (pCore p G).subtype := by
      rw [map_map, map_map]; rfl
    _ = (⊤ : Subgroup (pCore p G)).map (pCore p G).subtype := congrArg _ he
    _ = pCore p G := by rw [← MonoidHom.range_eq_map, range_subtype]

universe u

/-- B.5.2(1--2): construct a finite SQTK cover with nilpotent Fitting preimage
and nilpotent odd-order kernel. The quotient equivalence is compatible with
its surjection, and each Sylow three-subgroup of the three-core preimage is
normal in the cover and maps onto the three-core. No closure assumption on
`K` is needed: the given K-group property passes to subgroups and quotients. -/
public theorem exists_sqtk_cover {X Y : Type u} [Group X] [Finite X] [Group Y] [Finite Y]
    {K : GroupClass.{u}} (hX : IsSQTK K X) (f₀ : X →* Y)
    (hf₀ : Function.Surjective f₀) :
    ∃ (H' : Type u) (_ : Group H') (_ : Finite H') (f : H' →* Y),
      IsSQTK K H' ∧ Function.Surjective f ∧
      Group.IsNilpotent ((fittingSubgroup Y).comap f) ∧
      Group.IsNilpotent f.ker ∧ Odd (Nat.card f.ker) ∧
      (∃ e : H' ⧸ f.ker ≃* Y, ∀ x : H', e (QuotientGroup.mk' f.ker x) = f x) ∧
      ∀ P : Sylow 3 ((pCore 3 Y).comap f),
        (P.map ((pCore 3 Y).comap f).subtype).Normal ∧
          (P.map ((pCore 3 Y).comap f).subtype).map f = pCore 3 Y := by
  classical
  obtain ⟨U, hf, hmin⟩ := exists_minimal_surjection f₀ hf₀
  let f := f₀.comp U.subtype
  have hU := hX.subgroup U
  have hn : Group.IsNilpotent ((fittingSubgroup Y).comap f) :=
    nilpotent_preimage f hf hmin (fittingSubgroup Y)
  have hk : f.ker ≤ (fittingSubgroup Y).comap f := by
    intro x hx
    change f x ∈ fittingSubgroup Y
    rw [MonoidHom.mem_ker.mp hx]
    exact (fittingSubgroup Y).one_mem
  have hnker : Group.IsNilpotent f.ker := nilpotent_of_le hk
  let T : Sylow 2 f.ker := Classical.choice inferInstance
  let D : Subgroup U := T.map f.ker.subtype
  have : D.Normal := Sylow.normal_of_nilpotent_normal inferInstance hnker 2 T
  have hD : D ≤ f.ker := map_subtype_le _
  have hDtwo : IsPGroup 2 D := T.isPGroup'.map f.ker.subtype
  let g : U ⧸ D →* Y := QuotientGroup.lift D f hD
  have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective D f hf hD
  have hng : Group.IsNilpotent ((fittingSubgroup Y).comap g) :=
    nilpotent_preimage_lift f D hD (fittingSubgroup Y)
  have hngker : Group.IsNilpotent g.ker := by
    rw [QuotientGroup.ker_lift]
    exact Group.nilpotent_of_surjective ((QuotientGroup.mk' D).subgroupMap f.ker)
      ((QuotientGroup.mk' D).subgroupMap_surjective f.ker)
  have hcard : Nat.card g.ker = (T : Subgroup f.ker).index := by
    rw [QuotientGroup.ker_lift, ← relIndex_ker f.ker (QuotientGroup.mk' D),
      QuotientGroup.ker_mk']
    change ((T : Subgroup f.ker).map f.ker.subtype |>.comap f.ker.subtype).index = _
    rw [comap_map_eq_self_of_injective f.ker.subtype_injective]
  have hodd : Odd (Nat.card g.ker) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd, hcard]
    exact T.not_dvd_index
  have hsqtk : IsSQTK K (U ⧸ D) := by
    refine ⟨?_, hU.isKGroup.quotient D⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho D hDtwo).trans
      (hU.stronglyQuasithin p hp ho)
  refine ⟨U ⧸ D, inferInstance, inferInstance, g, hsqtk, hg, hng, hngker, hodd,
    ⟨QuotientGroup.quotientKerEquivOfSurjective g hg, fun _ => rfl⟩, ?_⟩
  exact fun P => sylow_pCore_preimage g hg 3 P

end CFSG.Quasithin.ChapterB.NilpotentCover
