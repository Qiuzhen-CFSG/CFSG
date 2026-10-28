module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.TerminalOvercomponent.TorusSource.Axes
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.AlternatingFiveBorel
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.OriginalSylow
public import Theory.GroupTheory.ConjugateOrbitIndexTwoStabilizer
/-!
# Both original torus commutator Sylows and their Borel normalizers

Actual Baumann placement and maximality identify Baumann with T intersect L₀,
so the source Borel normalizes it. Conjugation transports the natural block
Sylow calculation to the specified opposite component, without assuming that
the chosen torus is invariant under that conjugation. The index-two stabilizer
then preserves both literal Sylow--cubic Borels.

Source: Aschbacher--Smith 10.2.3(4), printed p.747. Both orientations and all
ambient intersections are retained.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual Baumann Sylow is the original orbit intersection. -/
theorem source_original_baumann_eq_orbit_sylow
    (hSO : baumann (T : Subgroup G) ≤ localOrbit T L)
    (hS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (localOrbit T L ⊔ baumann (T : Subgroup G))) :
    baumann (T : Subgroup G) = (T : Subgroup G) ⊓ localOrbit T L := by
  have hS' : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G)) (localOrbit T L) := by
    simpa only [sup_eq_left.mpr hSO] using hS
  exact ((Chapter1.isSylowIn_iff.mp hS').2.2 _
    (T.isPGroup'.to_le inf_le_left) (le_inf inf_le_left hSO) inf_le_right).symm

/-- The source Borel normalizes the actual common Baumann subgroup. -/
theorem source_original_borel_normalizes_baumann
    (hSO : baumann (T : Subgroup G) ≤ localOrbit T L)
    (hS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (localOrbit T L ⊔ baumann (T : Subgroup G))) :
    sourceOrbitBorel T L ≤ normalizer (baumann (T : Subgroup G) : Set G) := by
  rw [source_original_baumann_eq_orbit_sylow hSO hS]
  exact (map_subtype_le _).trans inf_le_right
end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter10
open Subgroup Theory.GroupTheory Chapter3.Section02 ChapterC ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The prescribed conjugate block has the literal torus commutator Sylow. -/
theorem source_original_conjugate_commutator_sylow
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hL : IsL2EvenBlock L 2) (hcore : pCore 2 L=blockU L)
    (hS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (localOrbit T L ⊔ baumann (T : Subgroup G)))
    (hSL : baumann (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G))
    (A : Subgroup G) (hAL : A ≤ L.map (MulAut.conj t).toMonoidHom)
    (hA : Nat.card A=3) (hAS : A ≤ normalizer (baumann (T : Subgroup G) : Set G)) :
    ⁅baumann (T : Subgroup G),A⁆=baumann (T : Subgroup G) ⊓ L.map (MulAut.conj t).toMonoidHom ∧
      Chapter1.IsSylowIn 2 ⁅baumann (T : Subgroup G),A⁆ (L.map (MulAut.conj t).toMonoidHom) := by
  let S := baumann (T : Subgroup G)
  let f := MulAut.conj t
  let A' := A.map f.symm.toMonoidHom
  have hA'L : A' ≤ L := by
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨l,hl,he⟩ := hAL ha
    have he' : f l=a := he
    change f.symm a ∈ L
    rw [←he',MulEquiv.symm_apply_apply]
    exact hl
  have hA' : Nat.card A'=3 := by
    rw [card_map_of_injective f.symm.injective]
    exact hA
  have hSn : t ∈ normalizer (S : Set G) :=
    normalizer_le_normalizer_baumann _ ((T : Subgroup G).le_normalizer ht)
  have hSf : S.map f.toMonoidHom=S := mem_normalizer_iff_map_conj_eq.mp hSn
  have hSg : S.map f.symm.toMonoidHom=S := by
    calc
      _ = (S.map f.toMonoidHom).map f.symm.toMonoidHom := congrArg (map f.symm.toMonoidHom) hSf.symm
      _ = S := by
        have hid : f.symm.toMonoidHom.comp f.toMonoidHom=MonoidHom.id G := by
          ext x
          exact f.symm_apply_apply x
        rw [map_map,hid,map_id]
  have hA'S : A' ≤ normalizer (S : Set G) := by
    have hh := map_mono (f:=f.symm.toMonoidHom) hAS
    rw [map_equiv_normalizer_eq,hSg] at hh
    exact hh
  have hAf : A'.map f.toMonoidHom=A := by
    ext x
    simp [A']
  obtain ⟨he,hP⟩ := source_original_natural_commutator_sylow D A' hL hcore hS hA'L hA' hA'S hSL
  have he' := congrArg (map f.toMonoidHom) he
  rw [map_commutator,hSf,hAf,map_inf _ _ _ f.injective,hSf] at he'
  have hP' := Chapter1.Section02.IndexTwo.isSylowIn_map hP f.toMonoidHom
  rw [map_commutator,hSf,hAf] at hP'
  exact ⟨he',hP'⟩

/-- The original stabilizer normalizes the whole opposite Borel. -/
theorem source_original_opposite_borel_normalized
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hL : IsL2EvenBlock L 2) (hcore : pCore 2 L=blockU L)
    (hS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (localOrbit T L ⊔ baumann (T : Subgroup G)))
    (hSL : baumann (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G))
    (A : Subgroup G) (hAL : A ≤ L.map (MulAut.conj t).toMonoidHom)
    (hA : Nat.card A=3) (hAS : A ≤ normalizer (baumann (T : Subgroup G) : Set G)) :
    (T : Subgroup G) ⊓ normalizer (L : Set G) ≤
      normalizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G) := by
  let J := L.map (MulAut.conj t).toMonoidHom
  let S := baumann (T : Subgroup G)
  have h := source_original_conjugate_commutator_sylow D hL hcore hS hSL ht A hAL hA hAS
  have hSP : Chapter1.IsSylowIn 2 (S ⊓ J) J := h.1 ▸ h.2
  let a : L ≃* J := (MulAut.conj t).subgroupMap L
  let eJ := (QuotientGroup.congr _ _ a.symm (pCore_map_iso 2 a.symm)).trans e
  have hRJ : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (J : Set G) :=
    index_two_stabilizer_normalizes_conjugate L (T : Subgroup G)
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn) ht
  have hRS : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (S : Set G) :=
    inf_le_left.trans ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _))
  rw [h.1]
  exact Chapter1.a5_sylow_cubic_borel_normalized J S A _ eJ hSP hAL hA hAS hRJ hRS
end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter10
open Subgroup Theory.GroupTheory Stellmacher Chapter3.Section02 ChapterC ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Both literal torus axes give full Sylows and stabilizer-invariant Borels. -/
theorem source_original_torus_both_sylow_borels
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)=⊥)
    (hL : IsL2EvenBlock L 2) (hcore : pCore 2 L=blockU L)
    (hSO : baumann (T : Subgroup G) ≤ localOrbit T L)
    (hS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (localOrbit T L ⊔ baumann (T : Subgroup G)))
    (hSL : baumann (T : Subgroup G) ≤ normalizer (L : Set G))
    (C : Subgroup G) (hCB : C ≤ sourceOrbitBorel T L) (hc : Nat.card C=9) :
    let hCR : C ≤ localOrbit T L := hCB.trans ((map_subtype_le _).trans inf_le_left)
    let q := (originalA5ProductProjection D e hn ht htn).comp (inclusion hCR)
    let D₁ := ((MonoidHom.snd _ _).comp q).ker.map C.subtype
    let D₂ := ((MonoidHom.fst _ _).comp q).ker.map C.subtype
    let S := baumann (T : Subgroup G)
    let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
    ⁅S,D₁⁆=S ⊓ L ∧ Chapter1.IsSylowIn 2 ⁅S,D₁⁆ L ∧
    ⁅S,D₂⁆=S ⊓ L.map (MulAut.conj t).toMonoidHom ∧
      Chapter1.IsSylowIn 2 ⁅S,D₂⁆ (L.map (MulAut.conj t).toMonoidHom) ∧
    R ≤ normalizer ((⁅S,D₁⁆ ⊔ D₁ : Subgroup G) : Set G) ∧
    R ≤ normalizer ((⁅S,D₂⁆ ⊔ D₂ : Subgroup G) : Set G) := by
  let hCR : C ≤ localOrbit T L := hCB.trans ((map_subtype_le _).trans inf_le_left)
  let q := (originalA5ProductProjection D e hn ht htn).comp (inclusion hCR)
  let D₁ := ((MonoidHom.snd _ _).comp q).ker.map C.subtype
  let D₂ := ((MonoidHom.fst _ _).comp q).ker.map C.subtype
  let S := baumann (T : Subgroup G)
  obtain ⟨hD₁L,hD₂J,hD₁,hD₂,_,_⟩ :=
    source_original_borel_torus_axes D e hn ht htn hb hz C hCB hc
  have hCS := hCB.trans (source_original_borel_normalizes_baumann hSO hS)
  have hD₁S : D₁ ≤ normalizer (S : Set G) := (map_subtype_le _).trans hCS
  have hD₂S : D₂ ≤ normalizer (S : Set G) := (map_subtype_le _).trans hCS
  obtain ⟨h₁,hP₁⟩ := source_original_natural_commutator_sylow D D₁ hL hcore hS hD₁L hD₁ hD₁S hSL
  obtain ⟨h₂,hP₂⟩ := source_original_conjugate_commutator_sylow D hL hcore hS hSL ht
    D₂ hD₂J hD₂ hD₂S
  refine ⟨h₁,hP₁,h₂,hP₂,?_,source_original_opposite_borel_normalized D e hn hL hcore hS hSL ht
    D₂ hD₂J hD₂ hD₂S⟩
  rw [h₁]
  exact Chapter1.a5_sylow_cubic_borel_normalized L S D₁ _ e (h₁ ▸ hP₁)
    hD₁L hD₁ hD₁S inf_le_right
    (inf_le_left.trans ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)))
end CFSG.Quasithin.Chapter10
