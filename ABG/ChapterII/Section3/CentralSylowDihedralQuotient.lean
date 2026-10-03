module

public import ABG.ChapterII.Section1.CentralQuotient
public import ABG.ChapterII.Section1.WreathedCentralQuotient
public import ABG.ChapterII.Section1.FusionPatterns
public import GorensteinWalter.Classification

/-!
# Dihedral Sylow subgroups in the quotient by a Sylow center

If a Sylow two-subgroup S of a finite group has dihedral quotient S/Z(S)
and the image of Z(S) is normal in the ambient group, quotienting by that
image gives dihedral Sylow two-subgroups. In the applications the Sylow
center is central in the whole group, which supplies the required normality.

The precise dihedral presentations of S/Z(S), proved in Chapter II Section 1,
identify the quotient Sylow image via the first isomorphism theorem. Sylow
conjugacy transports that model to every Sylow subgroup of the quotient.
This proves the Sylow-structure step of ABG Chapter II Section 3 Proposition 2
(article p22), and its actual-model form also applies to the generalized
Sylow shapes in Lemma 2 (article p24). The original semidihedral/wreathed
wrapper retains its statement and obtains the model from Chapter II Section 1.
-/

namespace ABG

variable {G : Type*} [Group G] [Finite G]

/-- An actual dihedral model of S/Z(S) gives dihedral Sylow subgroups
in the quotient by the ambient image of Z(S). -/
public theorem hasDihedralSylowTwo_quotient_sylow_center_of_model
    (S : Sylow 2 G) (N : Subgroup G) [N.Normal]
    (hN : N = subgroupCenter (S : Subgroup G))
    (he : ∃ m : ℕ, 1 ≤ m ∧
      Nonempty ((S ⧸ Subgroup.center S) ≃* DihedralGroup (2 ^ m))) :
    GorensteinWalter.HasDihedralSylowTwo (G ⧸ N) := by
  classical
  let q := QuotientGroup.mk' N
  let f : S →* G ⧸ N := q.comp (S : Subgroup G).subtype
  have hfker : f.ker = Subgroup.center S := by
    rw [show f.ker = N.comap (S : Subgroup G).subtype by
      simp [f, q, ← MonoidHom.comap_ker], hN]
    change ((Subgroup.center S).map (S : Subgroup G).subtype).comap
      (S : Subgroup G).subtype = Subgroup.center S
    exact Subgroup.comap_map_eq_self_of_injective (S : Subgroup G).subtype_injective _
  let T : Sylow 2 (G ⧸ N) := Sylow.mapSurjective (QuotientGroup.mk'_surjective N) S
  have hfrange : f.range = (T : Subgroup (G ⧸ N)) := by
    rw [Sylow.coe_mapSurjective]
    simp [f, q, MonoidHom.range_comp]
  let e : (S ⧸ Subgroup.center S) ≃* T :=
    (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hfrange))
  obtain ⟨m, hm, ⟨em⟩⟩ := he
  intro R
  exact ⟨m, hm, ⟨((Sylow.equiv R T).trans e.symm).trans em⟩⟩

/-- A normal Sylow center in the quasi-dihedral or wreathed case has an
ambient quotient with dihedral Sylow two-subgroups. -/
public theorem hasDihedralSylowTwo_quotient_sylow_center
    (S : Sylow 2 G) (N : Subgroup G) [N.Normal]
    (hN : N = subgroupCenter (S : Subgroup G))
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S) :
    GorensteinWalter.HasDihedralSylowTwo (G ⧸ N) := by
  apply hasDihedralSylowTwo_quotient_sylow_center_of_model S N hN
  rcases hS with hsemi | ⟨n, hn⟩
  · obtain ⟨n, hn, hc, a, b, ha, hb, hab, hg⟩ := hsemi
    exact ⟨n - 2, by omega,
      QuasiDihedral.central_quotient_equiv hn hc a b ha hb hab hg⟩
  · obtain ⟨P⟩ := Wreathed.nonempty_presentation hn
    exact ⟨n, by obtain ⟨hn, _⟩ := hn; omega, P.central_quotient_equiv⟩

end ABG
