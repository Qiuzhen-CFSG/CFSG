module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Generalized Fitting bounds through central covers

Under a surjection, normal nilpotent subgroups have normal nilpotent images,
and components have trivial or component images. Thus F* maps into F*.
For a finite central extension, the preimage of the target p-core is
nilpotent. Its normal Sylow p-subgroup maps onto that core and lies in the
source p-core. Hence the preimage is exactly the source p-core times the
central kernel, including its prime-to-p part.

These facts lift F*(H) ≤ Oₚ(H) to F*(G) ≤ Oₚ(G) ker(f). They do not assert
that a central cover is a specified standard group or discard its centre.
Source: the central-cover version of the proper-overgroup argument in
Aschbacher–Smith, combined manuscript of 1 March 2004, B.1.13,
printed p.74 (PDF p.85); component functoriality is supplied by
`ComponentCalculus` (GLS, vol. 2, Theorem 3.5 and Lemmas 3.9–3.10).
-/

public section
open Subgroup

namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H]

/-- Surjections carry the generalized Fitting subgroup into the target generalized Fitting subgroup. -/
theorem map_generalizedFitting_le_of_surjective (f : G →* H) (hf : Function.Surjective f) :
    (generalizedFitting G).map f ≤ generalizedFitting H := by
  rw [generalizedFitting, Subgroup.map_sup]
  apply sup_le
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply sSup_le
    rintro N ⟨hn, hnil⟩
    apply Subgroup.map_le_iff_le_comap.mp
    apply le_trans _ (fitting_le_generalizedFitting H)
    let := hnil
    exact le_sSup ⟨hn.map f hf,
      Group.nilpotent_of_surjective (f.subgroupMap N) (f.subgroupMap_surjective N)⟩
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply sSup_le
    intro N hn
    apply Subgroup.map_le_iff_le_comap.mp
    rcases hn.map_surjective f hf with hb | hc
    · exact hb ▸ bot_le
    · exact component_le_generalizedFitting H _ hc

end Theory.GroupTheory

namespace MonoidHom
variable {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Prime cores map onto prime cores across a finite central extension. -/
theorem map_pCore_of_central_kernel (f : G →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ center G) : (pCore p G).map f = pCore p H := by
  let : Finite H := Finite.of_surjective f hf
  apply le_antisymm
  · exact le_sSup ⟨Normal.map inferInstance f hf, pCore_isPGroup.map f⟩
  · let R := (pCore p H).comap f
    let g : R →* pCore p H := f.subgroupComap (pCore p H)
    have hg : Function.Surjective g := f.subgroupComap_surjective_of_surjective _ hf
    have hgc : g.ker ≤ center R := by
      intro x hx
      have hxk : (x : G) ∈ f.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hk hxk) y)
    let : Group.IsNilpotent (pCore p H) := (pCore_isPGroup (p := p) (G := H)).isNilpotent
    let : Group.IsNilpotent R := Subgroup.isNilpotent_of_ker_le_center g hgc
    let P : Sylow p R := Sylow.nonempty.some
    have hPn : ((P : Subgroup R).map R.subtype).Normal :=
      Sylow.normal_of_nilpotent_normal (inferInstance : R.Normal) inferInstance p P
    have hPc : (P : Subgroup R).map R.subtype ≤ pCore p G :=
      le_sSup ⟨hPn, P.isPGroup'.map R.subtype⟩
    have hPtop : (P.mapSurjective hg : Subgroup (pCore p H)) = ⊤ :=
      top_unique ((pCore_isPGroup.to_subgroup ⊤).le_sylow_of_normal _)
    have he := congrArg (Subgroup.map (pCore p H).subtype) hPtop
    change ((P : Subgroup R).map g).map (pCore p H).subtype = _ at he
    rw [map_map, ← MonoidHom.range_eq_map, range_subtype] at he
    change (P : Subgroup R).map (f.comp R.subtype) = pCore p H at he
    rw [← he, ← map_map]
    exact map_mono hPc

/-- The preimage of the target prime core retains precisely the central kernel. -/
theorem comap_pCore_of_central_kernel (f : G →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ center G) : (pCore p H).comap f = pCore p G ⊔ f.ker := by
  rw [← map_pCore_of_central_kernel f hf hk, comap_map_eq]

end MonoidHom

namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Lift a generalized Fitting bound through the actual surjection, retaining its central kernel. -/
theorem generalizedFitting_le_pCore_sup_ker_of_central_kernel
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ center G)
    (hH : generalizedFitting H ≤ pCore p H) :
    generalizedFitting G ≤ pCore p G ⊔ f.ker := by
  have h := Subgroup.map_le_iff_le_comap.mp
    ((map_generalizedFitting_le_of_surjective f hf).trans hH)
  rwa [f.comap_pCore_of_central_kernel hf hk] at h

end Theory.GroupTheory
