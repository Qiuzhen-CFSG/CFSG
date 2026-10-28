module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.Factor
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.LocalSylow
/-!
# The simultaneous Sylow arrangement in the plane normalizer

The symmetric factor normalizes its actual two-core V₁. The plane stabilizer
N_T(V₁) is Sylow in N_M(V₁), so a conjugation in that normalizer places a
Sylow two-subgroup of the factor inside T. Conjugate the cubic and the factor
together. The cubic stays Sylow in C_M(V₁), and the direct-product splitting,
symmetric-group equivalence, and two-core marking are transported by the
same ambient conjugation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the arrangement
in the setup of 15.3.60 on printed p.1150. The plane-normalizer Sylow fact
comes from the actual orthogonal action; no ambient normality is assumed.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
variable {G : Type*} [Group G]

private theorem centralizer_map_equiv (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom =
      centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

private theorem conjugate_two_subgroup_into_sylow [Finite G]
    (S : Sylow 2 G) (A : Subgroup G) (hA : IsPGroup 2 A) :
    ∃ n : G, A.map (MulAut.conj n).toMonoidHom ≤ S := by
  obtain ⟨R, hR⟩ := hA.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq G R S
  refine ⟨n, ?_⟩
  rw [← hn, Sylow.coe_subgroup_smul]
  exact map_mono hR

/-- Simultaneous conjugation inside the plane normalizer arranges the
symmetric factor's Sylow two-subgroup in the prescribed ambient Sylow group.
The cubic remains an actual Sylow three-subgroup of C_M(V₁). -/
theorem arrange_symmetric_factor [Finite G] {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (i : OrthogonalPlaneIndex)
    (PM3 : Sylow 3 (M ⊓ centralizer (d.plane i : Set G) : Subgroup G))
    (J : Subgroup G) (e : J ≃* Equiv.Perm (Fin 4)) (hJM : J ≤ M)
    (hd : Disjoint (planeCubic M (d.plane i) PM3) J)
    (hc : planeCubic M (d.plane i) PM3 ≤ centralizer (J : Set G))
    (hprod : M ⊓ centralizer (planeCubic M (d.plane i) PM3 : Set G) =
      planeCubic M (d.plane i) PM3 ⊔ J)
    (hcore : d.plane i = Stellmacher.twoCoreAmbient J) :
    ∃ (PM3' : Sylow 3 (M ⊓ centralizer (d.plane i : Set G) : Subgroup G))
      (J' : Subgroup G) (_ : J' ≃* Equiv.Perm (Fin 4)), J' ≤ M ∧
      Disjoint (planeCubic M (d.plane i) PM3') J' ∧
      planeCubic M (d.plane i) PM3' ≤ centralizer (J' : Set G) ∧
      M ⊓ centralizer (planeCubic M (d.plane i) PM3' : Set G) =
        planeCubic M (d.plane i) PM3' ⊔ J' ∧
      d.plane i = Stellmacher.twoCoreAmbient J' ∧
      ∃ Q : Sylow 2 J', factorSylow J' Q ≤ (T : Subgroup G) := by
  let N := M ⊓ normalizer (d.plane i : Set G)
  let S := planeStabilizer T (d.plane i)
  have hSN : S ≤ N := le_inf (inf_le_left.trans hTM) inf_le_right
  have hS2 : IsPGroup 2 S := T.isPGroup'.of_injective
    (inclusion (show S ≤ (T : Subgroup G) from inf_le_left)) (inclusion_injective _)
  let SN : Sylow 2 N := hS2.comap_subtype.toSylow
    (d.not_dvd_planeStabilizer_normalizer_relIndex T hTM i)
  have hJN : J ≤ N := by
    apply le_inf hJM
    rw [hcore]
    have hh := (pCore 2 J).le_normalizer_map J.subtype
    rw [(pCore 2 J).normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  let Q : Sylow 2 J := Classical.choice inferInstance
  let A := factorSylow J Q
  have hAN : A ≤ N := (factorSylow_le J Q).trans hJN
  obtain ⟨n, hn⟩ := conjugate_two_subgroup_into_sylow SN (A.subgroupOf N)
    (factorSylow_isPGroup J Q).comap_subtype
  let φ : G ≃* G := MulAut.conj (n : G)
  have hMmap : M.map φ.toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer n.property.1)
  have hVmap : (d.plane i).map φ.toMonoidHom = d.plane i :=
    mem_normalizer_iff_map_conj_eq.mp n.property.2
  have hAmap : A.map φ.toMonoidHom ≤ (T : Subgroup G) := by
    have hh := map_mono (f := N.subtype) hn
    have he : N.subtype.comp (MulAut.conj n).toMonoidHom = φ.toMonoidHom.comp N.subtype := by
      ext x; rfl
    rw [map_map, he, ← map_map, map_subgroupOf_eq_of_le hAN] at hh
    have hSmap : (SN : Subgroup N).map N.subtype = S := map_subgroupOf_eq_of_le hSN
    rw [hSmap] at hh
    exact hh.trans inf_le_left
  let L := M ⊓ centralizer (d.plane i : Set G)
  let D := planeCubic M (d.plane i) PM3
  let D' := D.map φ.toMonoidHom
  have hLmap : L.map φ.toMonoidHom = L := by
    change (M ⊓ centralizer (d.plane i : Set G)).map φ.toMonoidHom = _
    rw [map_inf _ _ _ φ.injective, hMmap, centralizer_map_equiv, hVmap]
  have hDL : D ≤ L := map_subtype_le _
  have hD'L : D' ≤ L := hLmap ▸ map_mono hDL
  have hD'2 : IsPGroup 3 D' := (PM3.isPGroup'.map L.subtype).map φ.toMonoidHom
  have hD'idx : ¬ 3 ∣ D'.relIndex L := by
    change ¬ 3 ∣ (D.map φ.toMonoidHom).relIndex L
    rw [← hLmap, relIndex_map_map_of_injective _ _ φ.injective]
    change ¬ 3 ∣ ((PM3 : Subgroup L).map L.subtype).relIndex L
    rw [relIndex, subgroupOf_map_subtype_eq]
    exact PM3.not_dvd_index
  let PM3' : Sylow 3 L := hD'2.comap_subtype.toSylow hD'idx
  have hD' : planeCubic M (d.plane i) PM3' = D' := map_subgroupOf_eq_of_le hD'L
  let J' := J.map φ.toMonoidHom
  let eJ : J ≃* J' := φ.subgroupMap J
  let Q' : Sylow 2 J' := Q.mapSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hQ' : factorSylow J' Q' = A.map φ.toMonoidHom := by
    change ((Q : Subgroup J).map eJ.toMonoidHom).map J'.subtype = _
    rw [map_map]
    change _ = ((Q : Subgroup J).map J.subtype).map φ.toMonoidHom
    rw [map_map]
    rfl
  have hJ'M : J' ≤ M := hMmap ▸ map_mono hJM
  have hd' : Disjoint D' J' := disjoint_map φ.injective hd
  have hc' : D' ≤ centralizer (J' : Set G) := by
    have hh := map_mono (f := φ.toMonoidHom) hc
    rwa [centralizer_map_equiv] at hh
  have hprod' : M ⊓ centralizer (D' : Set G) = D' ⊔ J' := by
    have hh := congrArg (Subgroup.map φ.toMonoidHom) hprod
    rw [map_inf _ _ _ φ.injective, hMmap, centralizer_map_equiv, Subgroup.map_sup] at hh
    exact hh
  have hcore' : d.plane i = Stellmacher.twoCoreAmbient J' := by
    have hh := congrArg (Subgroup.map φ.toMonoidHom) hcore
    rw [hVmap] at hh
    change d.plane i = ((pCore 2 J).map J.subtype).map φ.toMonoidHom at hh
    rw [map_map] at hh
    change d.plane i = (pCore 2 J').map J'.subtype
    rw [← pCore_map_iso 2 eJ, map_map]
    exact hh
  refine ⟨PM3', J', eJ.symm.trans e, hJ'M, ?_, ?_, ?_, hcore', Q', ?_⟩
  · rwa [hD']
  · rwa [hD']
  · rwa [hD']
  · rw [hQ']
    exact hAmap

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
