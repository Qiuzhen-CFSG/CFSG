module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterFusionGeometrySource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterCentralSylowSource
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugateSpan
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Aligning the original elementary product and its normalizer

First conjugate an elementary subgroup of the module's order onto U.
The natural L-action moves a nonidentity point of its distinguished-Z
conjugate back into Z; the TI property then aligns the whole subgroup.
Thus the normalizing centralizer product enters N(U) ∩ C(Z), where the
literal embedded Sylow theorem identifies a product of R's order with
a conjugate of R.

Source: Aschbacher–Smith, 2.4.21, printed p.536.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

private theorem conjugate_eq_sylow_image
    (N : Subgroup G) (P : Sylow 2 N) (R W : Subgroup G)
    (hP : (P : Subgroup N).map N.subtype=R)
    (hWN : W≤N) (hW : IsPGroup 2 W) (hc : Nat.card W=Nat.card R) :
    ∃ g : G, W.conjBy g=R := by
  obtain ⟨Q,hWQ⟩ := (hW.comap_subtype (K:=N)).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq N Q P
  refine ⟨g,eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨w,hw,rfl⟩
    rw [←hP]
    have hm : (MulAut.conj g) ⟨w,hWN hw⟩ ∈ (P : Subgroup N) := by
      rw [←hg]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hWQ hw)
    exact mem_map_of_mem N.subtype hm
  · change Nat.card R ≤ Nat.card (W.map (MulAut.conj (g:G)).toMonoidHom)
    rw [card_map_of_injective (MulAut.conj (g:G)).injective,hc]

/-- An elementary conjugate of U containing Z can be aligned while preserving Z. -/
theorem source_centerless_elementary_pair_alignment
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype)=⊥)
    (V : Subgroup G) (hV : IsElementaryAbelian 2 V)
    (hc : Nat.card V=Nat.card (sourceModule (d.block.map d.H.subtype)))
    (hZV : distinguishedZ d ≤ V) (z : G) (hzZ : z∈distinguishedZ d) (hz1 : z≠1) :
    ∃ f : G, V.conjBy f=sourceModule (d.block.map d.H.subtype) ∧
      (distinguishedZ d).conjBy f=distinguishedZ d := by
  let L := d.block.map d.H.subtype
  let U := sourceModule L
  let Z := distinguishedZ d
  obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
  have hZU : Z≤U := by
    rw [show Z=distinguishedZ d from rfl,distinguishedZ_of_centerless d hz]
    exact (source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS).ge.trans inf_le_left
  have hLN : L ≤ normalizer (U : Set G) :=
    L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L))
  obtain ⟨b,hb⟩ := source_maximum_elementary_conjugate d hG T hST hsingle hL hM hTM hunique V hV hc
  have hbu : b*z*b⁻¹∈U := by
    change b*z*b⁻¹∈sourceModule (d.block.map d.H.subtype)
    rw [←hb]
    exact mem_map_of_mem (MulAut.conj b).toMonoidHom (hZV hzZ)
  have hb1 : b*z*b⁻¹≠1 := fun he => hz1 ((MulAut.conj b).map_eq_one_iff.mp he)
  obtain ⟨l,hl,he⟩ := source_centerless_module_transitive d hL hz _ hbu hb1 z (hZU hzZ) hz1
  refine ⟨l*b,?_,?_⟩
  · change V.conjBy (l*b)=U
    rw [conjBy_mul]
    change (V.map (MulAut.conj b).toMonoidHom).conjBy l=U
    rw [hb]
    exact mem_normalizer_iff_map_conj_eq.mp (hLN hl)
  · have hzmap : z∈Z.conjBy (l*b) := by
      rw [conjBy_mul]
      exact ⟨b*z*b⁻¹,mem_map_of_mem (MulAut.conj b).toMonoidHom hzZ,he⟩
    have heq := (source_distinguished_TI d hG T hST hsingle hL hM hTM hunique).conjugate_eq_of_common_point
      (l*b) 1 z hz1 hzmap (by change z∈(distinguishedZ d).conjBy 1; rw [conjBy_one];exact hzZ)
    change (distinguishedZ d).conjBy (l*b)=(distinguishedZ d).conjBy 1 at heq
    simpa only [conjBy_one] using heq

/-- The normalizing product of the source order is a conjugate of the original R. -/
theorem source_centerless_normalizing_product_conjugate
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype)=⊥)
    (V W : Subgroup G) (hV : IsElementaryAbelian 2 V)
    (hcV : Nat.card V=Nat.card (sourceModule (d.block.map d.H.subtype)))
    (hZV : distinguishedZ d≤V) (z : G) (hzZ : z∈distinguishedZ d) (hz1 : z≠1)
    (hW : IsPGroup 2 W) (hWN : W≤normalizer (V : Set G))
    (hWC : W≤centralizer (distinguishedZ d : Set G))
    (hcW : Nat.card W=Nat.card (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))) :
    ∃ h : G, W=(Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).conjBy h := by
  let U := sourceModule (d.block.map d.H.subtype)
  let Z := distinguishedZ d
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let C := normalizer (U : Set G) ⊓ centralizer (Z : Set G)
  obtain ⟨f,hfV,hfZ⟩ := source_centerless_elementary_pair_alignment d hG T hST hsingle hL hM hTM hunique hz V hV hcV hZV z hzZ hz1
  obtain ⟨P,hP⟩ := source_module_normalizer_center_centralizer_sylow d hG T hST hsingle hL hM hTM hunique
  have hm : W.conjBy f≤C := by
    apply le_inf
    · have hh := map_mono hWN (f:=(MulAut.conj f).toMonoidHom)
      rw [map_equiv_normalizer_eq] at hh
      change W.conjBy f≤normalizer (V.conjBy f : Set G) at hh
      rw [hfV] at hh
      exact hh
    · have hh := (map_mono hWC (f:=(MulAut.conj f).toMonoidHom)).trans
        (map_centralizer_le_centralizer_image (Z : Set G) (MulAut.conj f).toMonoidHom)
      change W.conjBy f≤centralizer (Z.conjBy f : Set G) at hh
      rw [hfZ] at hh
      exact hh
  obtain ⟨b,hb⟩ := conjugate_eq_sylow_image C P R (W.conjBy f) hP hm (hW.map _) (by
    change Nat.card (W.map (MulAut.conj f).toMonoidHom)=Nat.card R
    rw [card_map_of_injective (MulAut.conj f).injective];exact hcW)
  have he : W.conjBy (b*f)=R := by rw [conjBy_mul];exact hb
  refine ⟨(b*f)⁻¹,?_⟩
  have hh := congrArg (fun A : Subgroup G=>A.conjBy (b*f)⁻¹) he
  rwa [conjBy_inv] at hh
end CFSG.Quasithin.Chapter2.LinearShadows.Single
