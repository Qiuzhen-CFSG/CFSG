module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryCanonicalResidual
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.NormalSymmetricThreeSupplement
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# The invariant full cover of the original escape factor

The canonical identity O²(P) = O^{3′}(I) makes the original residual
invariant under N = N_G(Z_S). In N/O₂(N), reconstruction from this residual
fixes the full S₃, L₃(2), or S₅ image. Thus its full preimage
K = P O₂(N) is normal in N. Its two-core is exactly O₂(N), and its quotient
is the original P/O₂(P). This keeps the ambient two-core explicitly;
normality of P itself is not needed.

The source cubic puts O₂(N) inside I, so K acts on the same original
W/Z_S through the original conjugation map. The image is unchanged and
the kernel is O₂(K). In the S₃ row, adjoining the original Sylow T preserves
the S₃ quotient and gives the literal index |PT:T| = 3.

Source: Aschbacher–Smith 6.1.19, printed p.675, the invariant-parabolic
step after O²(P) = O^{3′}(I). This supplies an invariant cover and the
symmetric-three Sylow extension; it does not assert that the required
parabolic escapes M or that the amalgam contradiction is established.
Those steps, initial 6.1.4–5 and the remaining escaping geometry stay
with qt-d-1222-rankone-recognition-natural, the owner of final 6.1.27 assembly.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalInvariantCover
variable {A : Type*} [Group A] [Finite A]

private theorem cover_normal (B C : Subgroup A) [C.Normal]
    (hBC : B ≤ C) (hCB : C ≤ normalizer (B : Set A))
    (hD : ((pResidual 2 B).map B.subtype).Normal)
    (hm : let X := B.map (QuotientGroup.mk' (pCore 2 A))
      Nonempty (X ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (X ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
      Nonempty (X ≃* Equiv.Perm (Fin 5))) :
    (B ⊔ pCore 2 A).Normal := by
  let q := QuotientGroup.mk' (pCore 2 A)
  let X := B.map q
  let Y := C.map q
  have hq := QuotientGroup.mk'_surjective (pCore 2 A)
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hcore : pCore 2 (A ⧸ pCore 2 A) = ⊥ := by
    apply comap_injective hq
    rw [q.comap_pCore_of_ker_isPGroup hq hk, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  let : Y.Normal := Normal.map inferInstance q hq
  have hYcore : pCore 2 Y = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : Y.Normal).isSubnormal,hcore]
    exact (MonoidHom.ker_eq_bot_iff Y.subtype).mpr Y.subtype_injective
  have hYX : Y ≤ normalizer (X : Set (A ⧸ pCore 2 A)) :=
    (map_mono hCB).trans (B.le_normalizer_map q)
  have hXY : X ≤ Y := map_mono hBC
  let : (X.subgroupOf Y).Normal := normal_subgroupOf_of_le_normalizer hYX
  have hXsub : X.IsSubnormal := by
    have hh := (inferInstance : (X.subgroupOf Y).Normal).isSubnormal.trans'
      (inferInstance : Y.Normal).isSubnormal
    rwa [map_subgroupOf_eq_of_le hXY] at hh
  let D := (pResidual 2 B).map B.subtype
  let : D.Normal := hD
  have hDX : D.map q = (pResidual 2 X).map X.subtype := map_embedded_pResidual 2 B q
  have hDXn : ((pResidual 2 X).map X.subtype).Normal := by
    rw [←hDX]
    exact Normal.map inferInstance q hq
  let := hDXn
  have hXn : X.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    intro c _
    exact NaturalFullFactor.normalizes_of_normalizes_residual Y X inferInstance hXY hXsub
      hYcore ((map_subtype_le _).trans hYX) hm c (by rw [normalizer_eq_top]; trivial)
  let := hXn
  have hh : (X.comap q).Normal := inferInstance
  simpa only [X,comap_map_eq,q,QuotientGroup.ker_mk'] using hh

private theorem cover_core (B : Subgroup A) (hn : (B ⊔ pCore 2 A).Normal) :
    (B ⊔ pCore 2 A).pCoreIn 2 = pCore 2 A := by
  let := hn
  apply le_antisymm
  · exact pCoreIn_le_of_subnormal 2 (inferInstance : (B ⊔ pCore 2 A).Normal).isSubnormal
  · exact le_pCoreIn_of_normalizes pCore_isPGroup le_sup_right le_normalizer_of_normal

private def cover_quotient (B : Subgroup A) :
    ((B ⊔ pCore 2 A : Subgroup A) ⧸ pCore 2 (B ⊔ pCore 2 A : Subgroup A)) ≃*
      (B ⧸ pCore 2 B) := by
  let q := QuotientGroup.mk' (pCore 2 A)
  have hq := QuotientGroup.mk'_surjective (pCore 2 A)
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have he : (B ⊔ pCore 2 A).map q = B.map q := by
    rw [Subgroup.map_sup,show (pCore 2 A).map q = ⊥ from QuotientGroup.map_mk'_self _,sup_bot_eq]
  let e := MulEquiv.subgroupCongr he
  exact ((q.subgroupMap (B ⊔ pCore 2 A)).pCoreQuotientEquiv
    (q.subgroupMap_surjective _) (by rw [ker_subgroupMap]; exact hk.comap_subtype)).trans
      ((QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
        ((q.subgroupMap B).pCoreQuotientEquiv
          (q.subgroupMap_surjective _) (by rw [ker_subgroupMap]; exact hk.comap_subtype)).symm)

/-- The original factor, enlarged by the ambient two-core, is normalized by
all of N. Its exact two-core and quotient retain the original factor model. -/
theorem invariant_cover_of_residual (P I N : Subgroup A)
    (hPI : P ≤ I) (hPN : P ≤ N)
    (hIP : I ≤ normalizer (P : Set A))
    (hI : (I.subgroupOf N).Normal)
    (hND : N ≤ normalizer ((pResidual 2 P).map P.subtype : Set A))
    (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)) (hj : Function.Injective j)
    (hje : ∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
      QuotientGroup.mk' (pCore 2 N) (inclusion hPN p))
    (hm : Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5))) :
    let K := P ⊔ N.pCoreIn 2
    N ≤ normalizer (K : Set A) ∧ K.pCoreIn 2 = N.pCoreIn 2 ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* (P ⧸ pCore 2 P)) := by
  let B := P.subgroupOf N
  let C := I.subgroupOf N
  let Q := pCore 2 N
  let q := QuotientGroup.mk' Q
  let K := P ⊔ N.pCoreIn 2
  have hBC : B ≤ C := subgroupOf_mono N hPI
  have hCB : C ≤ normalizer (B : Set N) := by
    rw [←subgroupOf_normalizer_eq hPN]
    exact fun x hx => hIP hx
  have hDmap : ((pResidual 2 B).map B.subtype).map N.subtype =
      (pResidual 2 P).map P.subtype := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hPN]
  have hDle : (pResidual 2 P).map P.subtype ≤ N := (map_subtype_le _).trans hPN
  have hD : ((pResidual 2 B).map B.subtype).Normal := by
    have he : (pResidual 2 B).map B.subtype =
        ((pResidual 2 P).map P.subtype).subgroupOf N := by
      apply map_injective N.subtype_injective
      rw [map_subgroupOf_eq_of_le hDle,hDmap]
    rw [he]
    exact normal_subgroupOf_of_le_normalizer hND
  have himage : B.map q = j.range := by
    apply le_antisymm
    · rintro _ ⟨p,hp,rfl⟩
      exact ⟨QuotientGroup.mk' (pCore 2 P) ⟨p,hp⟩,hje _⟩
    · rintro _ ⟨x,rfl⟩
      obtain ⟨p,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 P) x
      rw [hje]
      exact mem_map_of_mem q p.property
  have hm' : Nonempty (B.map q ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (B.map q ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
      Nonempty (B.map q ≃* Equiv.Perm (Fin 5)) := by
    let e := (MulEquiv.subgroupCongr himage).trans (MonoidHom.ofInjective hj).symm
    rcases hm with hm | hm | hm
    · obtain ⟨f⟩ := hm
      exact Or.inl ⟨e.trans f⟩
    · obtain ⟨f⟩ := hm
      exact Or.inr (Or.inl ⟨e.trans f⟩)
    · obtain ⟨f⟩ := hm
      exact Or.inr (Or.inr ⟨e.trans f⟩)
  let := hI
  have hn := cover_normal B C hBC hCB hD hm'
  have he : (B ⊔ Q).map N.subtype = K := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hPN]
    rfl
  let eK : (B ⊔ Q : Subgroup N) ≃* K :=
    ((B ⊔ Q).equivMapOfInjective N.subtype N.subtype_injective).trans
      (MulEquiv.subgroupCongr he)
  let eP := subgroupOfEquivOfLe hPN
  have hnK : N ≤ normalizer (K : Set A) := by
    rw [←he]
    have hh := (B ⊔ Q).le_normalizer_map N.subtype
    let := hn
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hcK : K.pCoreIn 2 = N.pCoreIn 2 := by
    have hh := congrArg (map N.subtype) (cover_core B hn)
    rw [map_pCoreIn_of_injective 2 _ _ N.subtype_injective,he] at hh
    exact hh
  exact ⟨hnK,hcK,⟨(QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).symm.trans
    ((cover_quotient B).trans (QuotientGroup.congr _ _ eP (pCore_map_iso 2 eP)))⟩⟩

/-- In the symmetric-three row the original P and T already generate a
local group with symmetric-three quotient and Sylow index three. -/
theorem cubic_sylow_extension (T : Sylow 2 A) (P N : Subgroup A)
    (hTN : (T : Subgroup A) ≤ N)
    (hn : N ≤ normalizer ((P ⊔ N.pCoreIn 2 : Subgroup A) : Set A))
    (e : ((P ⊔ N.pCoreIn 2 : Subgroup A) ⧸
      pCore 2 (P ⊔ N.pCoreIn 2 : Subgroup A)) ≃* (P ⧸ pCore 2 P))
    (hP : Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))) :
    Nonempty (((P ⊔ (T : Subgroup A) : Subgroup A) ⧸
      pCore 2 (P ⊔ (T : Subgroup A) : Subgroup A)) ≃* Equiv.Perm (Fin 3)) ∧
      (T : Subgroup A).relIndex (P ⊔ (T : Subgroup A)) = 3 := by
  let K := P ⊔ N.pCoreIn 2
  let H := P ⊔ (T : Subgroup A)
  have hcoreT : N.pCoreIn 2 ≤ (T : Subgroup A) := by
    have hh := pCoreIn_le_sylow N (T.subtype hTN)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN] at hh
  have hKH : K ≤ H := sup_le le_sup_left (hcoreT.trans le_sup_right)
  have hTH : (T : Subgroup A) ≤ H := le_sup_right
  have hHK : H ≤ normalizer (K : Set A) :=
    sup_le (le_sup_left.trans K.le_normalizer) (hTN.trans hn)
  let C := K.subgroupOf H
  let S := (T : Subgroup A).subgroupOf H
  let : C.Normal := normal_subgroupOf_of_le_normalizer hHK
  have hgen : C ⊔ S = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hKH,map_subgroupOf_eq_of_le hTH,
      ←MonoidHom.range_eq_map,range_subtype]
    exact le_antisymm (sup_le hKH hTH) (sup_le_sup le_sup_left le_rfl)
  let eC := subgroupOfEquivOfLe hKH
  obtain ⟨eP⟩ := hP
  obtain ⟨eH⟩ := NormalSymmetricThree.quotient_symmetricThree_of_normal_twoGroup_supplement
    C S ((QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)).trans (e.trans eP))
    T.isPGroup'.comap_subtype hgen
  exact ⟨⟨eH⟩,SymmetricThreeTwoCore.sylow_index_three eH (T.subtype hTH)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalInvariantCover

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
/-- The full cover, its exact original action image and two-core, and the
symmetric-three extension by the original Sylow. -/
@[expose] def NaturalInvariantCoverData {G X : Type*} [Group G] [Group X]
    (T : Sylow 2 G) (P I N : Subgroup G) (σ : I →* MulAut X) (hPI : P ≤ I) : Prop :=
  let K := P ⊔ N.pCoreIn 2
  let g := σ.comp (inclusion hPI)
  ∃ hKI : K ≤ I,
    N ≤ normalizer (K : Set G) ∧
    (T : Subgroup G) ≤ normalizer (K : Set G) ∧
    K.pCoreIn 2 = N.pCoreIn 2 ∧
    Nonempty ((K ⧸ pCore 2 K) ≃* (P ⧸ pCore 2 P)) ∧
    (σ.comp (inclusion hKI)).range = g.range ∧
    (σ.comp (inclusion hKI)).ker = pCore 2 K ∧
    (Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) →
      Nonempty (((P ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (P ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      (T : Subgroup G).relIndex (P ⊔ (T : Subgroup G)) = 3)
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterG.Section06 CFSG.Quasithin.ChapterE
open scoped IsMulCommutative Classical
universe v
variable {G : Type v} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
namespace NaturalEscapeGraph.OddConfiguration
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d

/-- On the same original marked action, the full factor cover is invariant
under the entire central-line normalizer, including T. The symmetric-three
row gives the literal group generated by P and T with Sylow index three. -/
theorem exists_ambient_invariant_cover
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let N := Escape.H (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧
      ∃ (hPI : P ≤ I) (hPN : P ≤ N) (_hIN : I ≤ N)
        (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hZ : (Z.subgroupOf W).Normal),
      let := hZ
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        let := hX
        IsElementaryAbelian 2 ((E.subgroupOf I).map σ) ∧
        1 < Nat.card ((E.subgroupOf I).map σ) ∧
        Nat.card ((E.subgroupOf I).map σ) ≤ 4 ∧
        let g := σ.comp (inclusion hPI)
        ∃ (φ : (P ⧸ pCore 2 P) →* g.range)
          (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)),
          Function.Bijective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
          Function.Injective j ∧ j.range.IsSubnormal ∧
          (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
          (∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
            QuotientGroup.mk' (pCore 2 N) (inclusion hPN p)) ∧
          pCore 2 g.range = ⊥ ∧ g.ker = pCore 2 P ∧
            (Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5))) ∧
            ((pResidual 2 P).map P.subtype = (primeToResidual 3 I).map I.subtype) ∧
            (N ≤ Subgroup.normalizer ((pResidual 2 P).map P.subtype : Set G)) ∧
            NaturalInvariantCoverData T P I N σ hPI := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,_hgen,_product,_hsingle,_hsmall,hmodels,
      hcanonical,hnormal,_horiginal,_hfactor,_hres,_hact,_hfull,_hrange,_hlift,_e,_he,_hcoords⟩ :=
    d.exists_ambient_canonical_residual h hnat hE hs hNS hab
  let := hZ
  let := hX
  let I := Escape.I (T : Subgroup G) L R
  let N := Escape.H (T : Subgroup G) L R
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let P := conjugateSpanBy E I
  let K := P ⊔ N.pCoreIn 2
  obtain ⟨hNK,hcore,⟨eK⟩⟩ := NaturalInvariantCover.invariant_cover_of_residual P I N hPI hPN
    (le_normalizer_conjugateSpanBy E I)
    (normal_subgroupOf_centralizer_normalizer (ZS (T : Subgroup G) L R : Set G))
    hnormal j hj hje hmodels
  have hKI : K ≤ I := sup_le hPI
    (natural_four_normalizer_core_centralizes (hn ▸ h) (hn ▸ hnat))
  have hTK : (T : Subgroup G) ≤ Subgroup.normalizer (K : Set G) :=
    h.sylow_normalizes_ZS.trans hNK
  let Z := ZS (T : Subgroup G) L R
  let W := Escape.U (T : Subgroup G) L R ⊓ conjugateSpanBy Z (centralizer ({z} : Set G))
  let g := σ.comp (inclusion hPI)
  let gK := σ.comp (inclusion hKI)
  have hQI : N.pCoreIn 2 ≤ I := natural_four_normalizer_core_centralizes (hn ▸ h) (hn ▸ hnat)
  have hQcore : N.pCoreIn 2 ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 N) hQI
    (hIN.trans (N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N))))
  have hcI : (I.pCoreIn 2).subgroupOf I ≤ σ.ker :=
    quotient_conjugation_action_kills_commutator_layer I W Z (I.pCoreIn 2)
      hZ hIW ((commutator_mono inf_le_left le_rfl).trans (natural_escape_core h hnat).2) σ hσ
  have hQker : (N.pCoreIn 2).subgroupOf I ≤ σ.ker := (subgroupOf_mono I hQcore).trans hcI
  have hrangeK : gK.range = g.range := by
    change (σ.comp (inclusion hKI)).range = (σ.comp (inclusion hPI)).range
    rw [MonoidHom.range_comp,MonoidHom.range_comp,inclusion_range,inclusion_range]
    change ((P ⊔ N.pCoreIn 2).subgroupOf I).map σ = (P.subgroupOf I).map σ
    rw [subgroupOf_sup hPI hQI,Subgroup.map_sup,(Subgroup.map_eq_bot_iff _).mpr hQker,sup_bot_eq]
  have hkerK : gK.ker = pCore 2 K := by
    have hle : pCore 2 K ≤ gK.ker := by
      intro k hk
      apply hQker
      have hh : (k : G) ∈ K.pCoreIn 2 := mem_map_of_mem K.subtype hk
      exact hcore ▸ hh
    have hi : gK.ker.index = (pCore 2 K).index := by
      rw [index_ker,hrangeK,index_eq_card,Nat.card_congr eK.toEquiv]
      exact (Nat.card_congr (MulEquiv.ofBijective φ hφ).toEquiv).symm
    have hc := (pCore 2 K).card_mul_index
    have hd := gK.ker.card_mul_index
    rw [hi] at hd
    have hp : 0 < (pCore 2 K).index := Nat.pos_of_ne_zero (pCore 2 K).index_ne_zero_of_finite
    have he : Nat.card (pCore 2 K) = Nat.card gK.ker :=
      mul_right_cancel₀ (ne_of_gt hp) (hc.trans hd.symm)
    exact (eq_of_le_of_card_ge hle he.ge).symm
  have hS3 := NaturalInvariantCover.cubic_sylow_extension T P N
    h.sylow_normalizes_ZS hNK eK
  exact ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,
    hcanonical,hnormal,hKI,hNK,hTK,hcore,⟨eK⟩,hrangeK,hkerK,hS3⟩

end NaturalEscapeGraph.OddConfiguration
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
