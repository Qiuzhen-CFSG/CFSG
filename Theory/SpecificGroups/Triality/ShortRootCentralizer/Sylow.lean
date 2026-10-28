module
public import Theory.SpecificGroups.Triality.ShortRootCentralizer.Containment
public import Theory.SpecificGroups.Triality.ParabolicLocalStructure

/-!
# The designated Sylow subgroup of a triality short-root centralizer

Native centralizer containment places every centralizing two-subgroup in the
central local factor. Its Levi projection has normal two-group kernel. The
central Levi centralizes the marked short root, so the Levi representatives
of the standard Sylow image already lie in its centralizer intersection.
Sylow maximality in the quotient, followed by the kernel preimage identity,
proves maximality of that exact intersection in the full centralizer.

Source: Aschbacher–Smith F.4.27(4)(ii) and F.4.40, printed pp.288 and 294
(`refs/quasithin.pdf`). This includes the prepared smallest case q = 4.
-/

public noncomputable section
open Subgroup
namespace Triality.Standard.ShortRootCentralizer
open Parabolics ConcreteBruhat RadicalCoordinates RadicalCoordinates.LeviCommutators

private theorem retract_sylow_bound {G Q : Type*} [Group G] [Group Q] [Finite G]
    (S : Sylow 2 G) (f : G →* Q) (hf : Function.Surjective f)
    (i : Q →* G) (hi : ∀ x, f (i x) = x) (hk : f.ker ≤ (S : Subgroup G))
    (D : Subgroup G) (hD : IsPGroup 2 D)
    (hrep : ∀ x ∈ (S : Subgroup G), i (f x) ∈ D) : D ≤ (S : Subgroup G) := by
  have hm : (S : Subgroup G).map f ≤ D.map f := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨i (f x),hrep x hx,hi _⟩
  have he := (S.mapSurjective hf).is_maximal' (hD.map f) hm
  have hh := map_le_iff_le_comap.mp he.le
  change D ≤ ((S : Subgroup G).map f).comap f at hh
  rwa [comap_map_eq_self hk] at hh

private theorem retract_mem_sylow {G Q : Type*} [Group G] [Group Q]
    (S : Subgroup G) (f : G →* Q) (i : Q →* G) (hi : ∀ x, f (i x) = x)
    (hk : f.ker ≤ S) (x : G) (hx : x ∈ S) : i (f x) ∈ S := by
  rw [←comap_map_eq_self hk]
  change f (i (f x)) ∈ S.map f
  rw [hi]
  exact mem_map_of_mem f hx

/-- The designated positive intersection is Sylow in the full short-root
centralizer. The proof uses native containment and the exact local Levi
projection; the positive centralizer order is not substituted for extremality. -/
theorem centralizer_sylow (n : ℕ) (hn : 0 < n) (hn2 : 1 < n)
    (t : ExtensionField (binaryParameters n hn)) (ht : t ≠ 0) :
    let P := binaryParameters n hn
    ∃ R : Sylow 2 (centralizer ({short P rfl 2 t} : Set (Carrier P))),
      (R : Subgroup _) = (unipotent P).subgroupOf
        (centralizer ({short P rfl 2 t} : Set (Carrier P))) := by
  let P := binaryParameters n hn
  let C := centralizer ({short P rfl 2 t} : Set (Carrier P))
  let F := localFactor P .central
  have hUC : IsPGroup 2 ((unipotent P).subgroupOf C) :=
    (unipotent_isPGroup_binary P rfl).comap_subtype
  refine ⟨⟨(unipotent P).subgroupOf C,hUC,?_⟩,rfl⟩
  intro D hD hUD
  apply le_antisymm ?_ hUD
  let A := D.map C.subtype
  have hAC : A ≤ C := map_subtype_le D
  have hAp : IsPGroup 2 A := hD.map C.subtype
  have hAF : A ≤ F := pSubgroup_le_localFactor P .central A hAp
    (hAC.trans (centralizer_le_central n hn hn2 t ht))
  let S := (unipotentSylow P rfl).subtype (unipotentSylow_le_localFactor P rfl .central)
  let f := localLeviProjection P rfl .central
  let i := inclusion (levi_le_localFactor P rfl .central)
  have hi (x : levi P .central) : f (i x) = x := localLeviProjection_inclusion P rfl .central x
  have hRU : radical P .central ≤ unipotent P := by
    rw [radical_eq_descendedRootSubgroup P rfl .central]
    exact descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P rfl .central)
  have hk : f.ker ≤ (S : Subgroup F) := by
    rw [show f.ker = (radical P .central).subgroupOf F from
      localLeviProjection_ker P rfl .central]
    exact fun x hx => hRU hx
  have hAS : A.subgroupOf F ≤ (S : Subgroup F) := by
    apply retract_sylow_bound S f (localLeviProjection_surjective P rfl .central)
      i hi hk (A.subgroupOf F) hAp.comap_subtype
    intro x hx
    have hu : i (f x) ∈ (S : Subgroup F) := retract_mem_sylow _ f i hi hk x hx
    have hc : (i (f x)).val ∈ C := levi_central_le_centralizer P rfl t (f x).property
    exact mem_map_of_mem C.subtype (hUD (show (⟨(i (f x)).val,hc⟩ : C) ∈
      (unipotent P).subgroupOf C from hu))
  intro x hx
  exact hAS (show (⟨x.val,hAF (mem_map_of_mem C.subtype hx)⟩ : F) ∈ A.subgroupOf F from
    mem_map_of_mem C.subtype hx)

end Triality.Standard.ShortRootCentralizer
