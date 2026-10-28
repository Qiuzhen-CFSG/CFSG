module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryThreeActionModel
/-!
# Individual Sylow invariance of the original binary-three parabolics

Use the natural GL3(2) action on the canonical moved subspace of the same
W/Z_S witness. Compatible automorphisms act inner, and the model Sylow is
self-normalizing, so they fix every overgroup of its two-kernel preimage.

The chosen z need not be central in the original T. A power of the original
fixed-free cubic rotates a T-fixed nonidentity vector of Z_S to z. The
rotated Sylow acts on W/Z_S and has the same intersection with the invariant
cover, because the cubic already fixes both parabolics. Transfer their
invariance back along that power to obtain individual T-invariance.
Adjoining T to the escaping parabolic gives a literal HStar(T,M) member,
an S3 two-core quotient, and index three over T.

The Chapter12 application discharges the marking and rotation premises on
the original witness. S5 escape, the amalgam contradiction, initial 6.1.4–5,
omega escape and the remaining geometry through unconditional 6.1.27 remain
with qt-d-1222-rankone-recognition-natural.

Source: Aschbacher–Smith 6.1.19, printed p.675 (`refs/quasithin.pdf`), using
G.6.4(2a). No full-factor normalization or stronger commutator bound is assumed.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open CFSG.Quasithin.ChapterG.Section06
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeAction
variable {A : Type*} [Group A] [Finite A]

private theorem cubic_transitive_four (hc : Nat.card A = 4)
    (α : MulAut A) (hα : α^3=1) (hfixed : ∀ x, α x=x → x=1)
    (x y : A) (hx : x ≠ 1) (hy : y ≠ 1) :
    y=x ∨ y=α x ∨ y=α (α x) := by
  classical
  let := Fintype.ofFinite A
  have hcycle : α (α (α x)) = x := congrArg (fun f : MulAut A => f x) hα
  have h12 : x ≠ α x := fun he => hx (hfixed x he.symm)
  have h23 : α x ≠ α (α x) := fun he => h12 (α.injective he)
  have h13 : x ≠ α (α x) := by
    intro he
    have hh : α x = x := (congrArg α he).trans hcycle
    exact hx (hfixed x hh)
  have h21 : α x ≠ 1 := fun he => hx (α.injective (he.trans α.map_one.symm))
  have h31 : α (α x) ≠ 1 := fun he => h21 (α.injective (he.trans α.map_one.symm))
  by_contra hh
  push Not at hh
  have hb := Finset.card_le_univ ({1,x,α x,α (α x),y} : Finset A)
  have hc' : Fintype.card A = 4 := (Nat.card_eq_fintype_card).symm.trans hc
  rw [hc'] at hb
  have hfive : ({1,x,α x,α (α x),y} : Finset A).card = 5 := by
    simp [h12,h13,h23,
      Ne.symm hx,Ne.symm h21,Ne.symm h31,Ne.symm hy,
      Ne.symm hh.1,Ne.symm hh.2.1,Ne.symm hh.2.2]
  omega

/-- A power of the fixed-free cubic carries the original Sylow into the
chosen involution centralizer, without changing the involution. -/
theorem exists_cubic_power_centralizing_sylow
    (T : Sylow 2 A) (Z : Subgroup A) (hZ : IsPGroup 2 Z)
    (hTZ : (T : Subgroup A) ≤ normalizer (Z : Set A))
    (hcard : Nat.card Z = 4) (z : A) (hz : z ∈ Z) (hz1 : z ≠ 1)
    (c : A) (hcZ : c ∈ normalizer (Z : Set A)) (hc3 : c^3=1)
    (hfixed : ∀ x ∈ Z, c*x*c⁻¹=x → x=1) :
    ∃ l ∈ zpowers c, (T : Subgroup A).map (MulAut.conj l).toMonoidHom ≤
      centralizer ({z} : Set A) := by
  have hn : Z ≠ ⊥ := by intro he; rw [he,card_bot] at hcard; omega
  obtain ⟨y,hy⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centralizer_ne_bot_of_pGroups (T : Subgroup A) Z T.isPGroup' hZ hTZ hn)
  let α := Z.normalizerMonoidHom ⟨c,hcZ⟩
  have hα : α^3=1 := by
    rw [←map_pow]
    have he : (⟨c,hcZ⟩ : normalizer (Z : Set A))^3=1 := Subtype.ext hc3
    rw [he,map_one]
  have hf (x : Z) (he : α x=x) : x=1 := Subtype.ext
    (hfixed x x.property (congrArg Subtype.val he))
  have hy1 : (y : A) ≠ 1 := fun he => hy (Subtype.ext he)
  have hz' : (⟨z,hz⟩ : Z) ≠ 1 := fun he => hz1 (congrArg Subtype.val he)
  obtain ⟨l,hl,he⟩ : ∃ l ∈ zpowers c, (MulAut.conj l) (y : A) = z := by
    rcases cubic_transitive_four hcard α hα hf ⟨y,y.property.1⟩ ⟨z,hz⟩
      (fun he => hy1 (congrArg Subtype.val he)) hz' with he | he | he
    · exact ⟨1,one_mem _,by simpa using (congrArg Subtype.val he).symm⟩
    · exact ⟨c,mem_zpowers c,(congrArg Subtype.val he).symm⟩
    · refine ⟨c*c,(zpowers c).mul_mem (mem_zpowers c) (mem_zpowers c),?_⟩
      change (c*c)*(y:A)*(c*c)⁻¹=z
      have hh := (congrArg Subtype.val he).symm
      change c*(c*(y:A)*c⁻¹)*c⁻¹=z at hh
      simpa only [mul_inv_rev,←mul_assoc] using hh
  refine ⟨l,hl,?_⟩
  rintro _ ⟨t,ht,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  change (MulAut.conj l) t * z = z * (MulAut.conj l) t
  have hh := congrArg (MulAut.conj l) (y.property.2 t ht)
  simpa only [map_mul,he] using hh

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeAction

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open scoped IsMulCommutative
open ChapterG.Section06 Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L M R : Subgroup G}

/-- The literal natural action and original cubic force T to fix both
parabolics, even when T does not centralize the marked involution. -/
theorem natural_three_pair_sylow_invariant
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (z : G) (hz : z ∈ ZS (T : Subgroup G) L R) (hz1 : z ≠ 1)
    (P : Subgroup G)
    (hPI : P ≤ Escape.I (T : Subgroup G) L R)
    (hIW : let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy (ZS (T : Subgroup G) L R) (centralizer ({z} : Set G))
      Escape.I (T : Subgroup G) L R ≤ normalizer (W : Set G))
    (hZ : let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy (ZS (T : Subgroup G) L R) (centralizer ({z} : Set G))
      ((ZS (T : Subgroup G) L R).subgroupOf W).Normal) :
    let I := Escape.I (T : Subgroup G) L R
    let N := Escape.H (T : Subgroup G) L R
    let Z := ZS (T : Subgroup G) L R
    let W := Escape.U (T : Subgroup G) L R ⊓ conjugateSpanBy Z (centralizer ({z} : Set G))
    let K := P ⊔ N.pCoreIn 2
    let := hZ
    ∀ (σ : I →* MulAut (W ⧸ Z.subgroupOf W)),
      (∀ i : I, ∀ w : W,
        σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
          QuotientGroup.mk' (Z.subgroupOf W)
            ⟨(i : G)*(w : G)*(i : G)⁻¹,(mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) →
      ∀ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
      let := hX
      let g := σ.comp (inclusion hPI)
      let θ := Representation.ofElementaryAbelianAction
        (A := g.range) (G := W ⧸ Z.subgroupOf W) (p := 2)
      NaturalInvariantCoverData T P I N σ hPI →
      Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) →
      HasModelOn θ ⊤ (subspaceCommutator θ ⊤ ⊤) (binaryLinearAction 3) →
      ∀ B C, NaturalThreeParabolicPair ((T : Subgroup G) ⊓ K) K B C →
      ∀ c : G, c ∈ N → c^3=1 →
        (∀ x ∈ Z, c*x*c⁻¹=x → x=1) →
        c ∈ normalizer (B : Set G) → c ∈ normalizer (C : Set G) →
        (T : Subgroup G) ≤ normalizer (B : Set G) ∧
          (T : Subgroup G) ≤ normalizer (C : Set G) := by
  intro I N Z W K instZ σ hσ hX instX g θ hcover hthree hmodel B C d c hcN hc3 hcf hcB hcC
  let := hZ
  let := hX
  obtain ⟨hKI,hNK,hTK,_,⟨eK⟩,hrange,hker,_⟩ := hcover
  obtain ⟨eP⟩ := hthree
  let f := σ.comp (inclusion hKI)
  let e : f.range ≃* BinaryLinear.OuterCyclic.LinearGroup 3 :=
    (QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans (eK.trans eP))
  let τ := Representation.ofElementaryAbelianAction
    (A := f.range) (G := W ⧸ Z.subgroupOf W) (p := 2)
  have hm : HasModelOn τ ⊤ (subspaceCommutator τ ⊤ ⊤) (binaryLinearAction 3) := by
    change (fun H : Subgroup (MulAut (W ⧸ Z.subgroupOf W)) =>
      let τ := Representation.ofElementaryAbelianAction (A := H) (G := W ⧸ Z.subgroupOf W) (p := 2)
      HasModelOn τ ⊤ (subspaceCommutator τ ⊤ ⊤) (binaryLinearAction 3)) f.range
    rw [hrange]
    exact hmodel
  have hZcard : Nat.card Z = 4 := (hnat.sylow_intersection_geometry T h.sylow_normalizes_L).1
  obtain ⟨l,hl,hTz⟩ := NaturalThreeAction.exists_cubic_power_centralizing_sylow
    T Z (T.isPGroup'.to_le h.ZS_le_T) h.sylow_normalizes_ZS hZcard z hz hz1
    c hcN hc3 hcf
  have hlB := (zpowers_le.mpr hcB) hl
  have hlC := (zpowers_le.mpr hcC) hl
  have hlN := (zpowers_le.mpr hcN) hl
  have hlK := hNK hlN
  have hlS : l ∈ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
    rw [←d.inf_eq]
    exact inf_normalizer_le_normalizer_inf ⟨hlB,hlC⟩
  let T' := T.mapSurjective (f := (MulAut.conj l).toMonoidHom) (MulAut.conj l).surjective
  have hT'N : (T' : Subgroup G) ≤ N := by
    rintro _ ⟨t,ht,rfl⟩
    exact N.mul_mem (N.mul_mem hlN (h.sylow_normalizes_ZS ht)) (N.inv_mem hlN)
  have hT'K : (T' : Subgroup G) ≤ normalizer (K : Set G) := hT'N.trans hNK
  have hKl : K.map (MulAut.conj l).toMonoidHom = K := mem_normalizer_iff_map_conj_eq.mp hlK
  have hS : (T' : Subgroup G) ⊓ K = (T : Subgroup G) ⊓ K := by
    calc
      (T' : Subgroup G) ⊓ K = ((T : Subgroup G) ⊓ K).map (MulAut.conj l).toMonoidHom := by
        rw [map_inf _ _ _ (MulAut.conj l).injective,hKl]
        rfl
      _ = (T : Subgroup G) ⊓ K := mem_normalizer_iff_map_conj_eq.mp hlS
  have fixed (D : Subgroup G) (hDK : D ≤ K) (hSD : (T : Subgroup G) ⊓ K ≤ D)
      (hlD : l ∈ normalizer (D : Set G)) : (T : Subgroup G) ≤ normalizer (D : Set G) := by
    have hT'D : (T' : Subgroup G) ≤ normalizer (D : Set G) := by
      intro t ht
      have htW : t ∈ normalizer (W : Set G) := inf_normalizer_le_normalizer_inf
        ⟨natural_escape_normalizer_normalizes_U h hE hNS (hT'N ht),
          le_normalizer_conjugateSpanBy Z (centralizer ({z} : Set G)) (hTz ht)⟩
      exact NaturalThreeAction.quotient_action_normalizes_parabolic T' K W Z D hT'K
        (hKI.trans hIW) f (fun k w => hσ (inclusion hKI k) w)
        (by rw [hker]; exact pCore_isPGroup) e hX hm hDK (hS.symm ▸ hSD)
        (hT'K ht) htW (hT'N ht)
        (inf_normalizer_le_normalizer_inf ⟨(T' : Subgroup G).le_normalizer ht,hT'K ht⟩)
    intro t ht
    have ht' : (MulAut.conj l) t ∈ (T' : Subgroup G) := mem_map_of_mem _ ht
    have hn := hT'D ht'
    exact (normalizer (D : Set G)).mul_mem_cancel_left hlD |>.mp
      ((normalizer (D : Set G)).mul_mem_cancel_right
        ((normalizer (D : Set G)).inv_mem hlD) |>.mp hn)
  exact ⟨fixed B d.left_lt.le d.left_above.le hlB,
    fixed C d.right_lt.le d.right_above.le hlC⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeAction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
private theorem cubic_overgroup_mem_HStar
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hHN : H ≤ Escape.H (T : Subgroup G) L R)
    (hHM : ¬ H ≤ M) (hi : (T : Subgroup G).relIndex H = 3) :
    H ∈ Chapter3.HStar (T : Subgroup G) M := by
  have hN : Escape.H (T : Subgroup G) L R ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal ⟨ZS (T : Subgroup G) L R,h.ZS_ne_bot,
      T.isPGroup'.to_le h.ZS_le_T,rfl⟩,h.sylow_normalizes_ZS⟩
  refine ⟨⟨Chapter3.mem_HOver_of_sylow_interval T hTH hHN hN,hHM⟩,?_⟩
  intro X hX hXH
  have hd : X.relIndex H ∣ 3 := hi ▸ relIndex_dvd_of_le_left H hX.1.2
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · exact relIndex_eq_one.mp h1
  · have hh := relIndex_mul_relIndex (T : Subgroup G) X H hX.1.2 hXH
    rw [h3,hi] at hh
    have hx : (T : Subgroup G).relIndex X = 1 := by omega
    exact False.elim (hX.2 ((relIndex_eq_one.mp hx).trans h.sylow_le))

private theorem escaping_cover
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    (hIout : ¬ Escape.I (T : Subgroup G) L R ≤ M)
    (E : Subgroup G) (hEtwo : IsPGroup 2 E) (hEI : E ≤ Escape.I (T : Subgroup G) L R)
    {X : Type*} [Group X]
    (σ : Escape.I (T : Subgroup G) L R →* MulAut X)
    (hPI : conjugateSpanBy E (Escape.I (T : Subgroup G) L R) ≤ Escape.I (T : Subgroup G) L R)
    (hnormal : Escape.H (T : Subgroup G) L R ≤ normalizer
      ((pResidual 2 (conjugateSpanBy E (Escape.I (T : Subgroup G) L R))).map
        (conjugateSpanBy E (Escape.I (T : Subgroup G) L R)).subtype : Set G))
    (hmodels : Nonempty (((conjugateSpanBy E (Escape.I (T : Subgroup G) L R)) ⧸
        pCore 2 (conjugateSpanBy E (Escape.I (T : Subgroup G) L R))) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (((conjugateSpanBy E (Escape.I (T : Subgroup G) L R)) ⧸
        pCore 2 (conjugateSpanBy E (Escape.I (T : Subgroup G) L R))) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
      Nonempty (((conjugateSpanBy E (Escape.I (T : Subgroup G) L R)) ⧸
        pCore 2 (conjugateSpanBy E (Escape.I (T : Subgroup G) L R))) ≃* Equiv.Perm (Fin 5)))
    (hcover : NaturalInvariantCoverData T (conjugateSpanBy E (Escape.I (T : Subgroup G) L R))
      (Escape.I (T : Subgroup G) L R) (Escape.H (T : Subgroup G) L R) σ hPI) :
    NaturalEscapingCoverData T (conjugateSpanBy E (Escape.I (T : Subgroup G) L R))
      (Escape.H (T : Subgroup G) L R) M := by
  let I := Escape.I (T : Subgroup G) L R
  let N := Escape.H (T : Subgroup G) L R
  let P := conjugateSpanBy E I
  let K := P ⊔ N.pCoreIn 2
  let H := P ⊔ (T : Subgroup G)
  have hPtwo : ¬ IsPGroup 2 P := by
    intro hp
    have hd := (NaturalCanonicalResidual.model_facts hmodels).1
    obtain ⟨k,hk⟩ := (hp.to_quotient (pCore 2 P)).exists_card_eq
    rw [hk] at hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hPout : ¬ P ≤ M := natural_escape_span_not_le_of_residual_invariant h hnat hE hs
    hIout E hEtwo
    hEI (h.sylow_normalizes_ZS.trans hnormal) hPtwo
  obtain ⟨hKI,hNK,hTK,hcore,eK,hrange,hker,hS3⟩ := hcover
  have hKout : ¬ K ≤ M := fun hc => hPout (le_sup_left.trans hc)
  have hHout : ¬ H ≤ M := fun hc => hPout (le_sup_left.trans hc)
  have hHN : H ≤ N := sup_le (hPI.trans (Subgroup.centralizer_le_normalizer _)) h.sylow_normalizes_ZS
  have hQT : N.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hTN : (T : Subgroup G) ≤ N := h.sylow_normalizes_ZS
    have hh := pCoreIn_le_sylow N (T.subtype hTN)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN] at hh
  have hHK : H = K ⊔ (T : Subgroup G) := by
    exact le_antisymm (sup_le_sup le_sup_left le_rfl)
      (sup_le (sup_le le_sup_left (hQT.trans le_sup_right)) le_sup_right)
  have hNH : N ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (H : Set G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hHK,Subgroup.map_sup,mem_normalizer_iff_map_conj_eq.mp (hNK hx.1),
      mem_normalizer_iff_map_conj_eq.mp hx.2]
  have hstar : Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) →
      H ∈ Chapter3.HStar (T : Subgroup G) M ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∧
      (T : Subgroup G).relIndex H = 3 := by
    intro he
    obtain ⟨hq,hi⟩ := hS3 he
    exact ⟨cubic_overgroup_mem_HStar h H le_sup_right hHN hHout hi,hq,hi⟩
  exact ⟨hPout,hKout,hHout,hHN,hNH,hstar⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeAction


namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeAction
variable {G : Type*} [Group G] [Finite G]

private theorem symmetric_three_sylow_extension (T : Sylow 2 G) (B : Subgroup G)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (eB : Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))) :
    Nonempty (((B ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (B ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      (T : Subgroup G).relIndex (B ⊔ (T : Subgroup G)) = 3 := by
  let H := B ⊔ (T : Subgroup G)
  have hBH : B ≤ H := le_sup_left
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  let D := B.subgroupOf H
  let S := (T : Subgroup G).subgroupOf H
  let : D.Normal := normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hTB)
  have hgen : D ⊔ S = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBH,map_subgroupOf_eq_of_le hTH,
      ←MonoidHom.range_eq_map,range_subtype]
  let eD := subgroupOfEquivOfLe hBH
  obtain ⟨eB⟩ := eB
  obtain ⟨eH⟩ := NormalSymmetricThree.quotient_symmetricThree_of_normal_twoGroup_supplement
    D S ((QuotientGroup.congr _ _ eD (pCore_map_iso 2 eD)).trans eB)
    T.isPGroup'.comap_subtype hgen
  exact ⟨⟨eH⟩,SymmetricThreeTwoCore.sylow_index_three eH (T.subtype hTH)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeAction
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G]

/-- The two source parabolics are individually invariant under T and the
original cubic; their first member escapes M. -/
@[expose] def NaturalThreeInvariantParabolicData
    (T : Sylow 2 G) (L R P N M : Subgroup G) : Prop :=
  Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) →
    let K := P ⊔ N.pCoreIn 2
    ∃ B C : Subgroup G, NaturalThreeParabolicPair ((T : Subgroup G) ⊓ K) K B C ∧
      (¬ B ≤ M) ∧ (T : Subgroup G) ≤ normalizer (B : Set G) ∧
      (T : Subgroup G) ≤ normalizer (C : Set G) ∧
      (B ⊔ (T : Subgroup G)) ∈ Chapter3.HStar (T : Subgroup G) M ∧
      Nonempty (((B ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (B ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      (T : Subgroup G).relIndex (B ⊔ (T : Subgroup G)) = 3 ∧
      ∃ c ∈ L, c ∈ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
        c ∈ N ∧ orderOf c = 3 ∧
        (∀ z ∈ ZS (T : Subgroup G) L R, c * z * c⁻¹ = z → z = 1) ∧
        c ∈ normalizer (B : Set G) ∧ c ∈ normalizer (C : Set G)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d
/-- On the same original W/Z_S witness, both L3(2) parabolics are fixed by
T and the cubic. The escaping first parabolic extends to an HStar member
with S3 two-core quotient and index three over T. -/
theorem exists_ambient_three_invariant_parabolic
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
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
            NaturalInvariantCoverData T P I N σ hPI ∧
            NaturalEscapingCoverData T P N M ∧
            NaturalFiveCubicParabolicData T L R P N ∧
            NaturalThreeInvariantParabolicData T L R P N M := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hmarked⟩ :=
    d.exists_ambient_marked_cover h hnat hE hs hNS hab
  let := hZ
  let := hX
  have hIout : ¬ Escape.I (T : Subgroup G) L R ≤ M := fun hc =>
    d.hstar.1.2 (d.overgroup.trans (sup_le hc h.sylow_le))
  have hescape := NaturalThreeAction.escaping_cover h hnat hE hs hIout
    ((layer L R).map (MulAut.conj a).toMonoidHom)
    ((T.isPGroup'.to_le h.layer_le_T).map (MulAut.conj a).toMonoidHom)
    hEI σ hPI hnormal hmodels hcover
  have hfive := natural_five_cubic_parabolic_of_invariant_cover
    (hn ▸ h) (hn ▸ hnat) _ σ hPI hcover
  have hthree := natural_three_cubic_parabolic_of_invariant_cover
    (hn ▸ h) (hn ▸ hnat) _ σ hPI hcover hescape
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,?_⟩
  intro he
  obtain ⟨B,C,dp,hBM,_,c,hcL,hcTL,hcN,hc3,hcf,hcB,hcC⟩ := hthree he
  have hinv := natural_three_pair_sylow_invariant (hn ▸ h) (hn ▸ hnat) hE hNS
    z hz (fun hz1 => by rw [hz1,orderOf_one] at ho; omega) _ hPI hIW hZ σ hσ hX
    hcover he (hmarked he) B C dp c hcN (hc3 ▸ pow_orderOf_eq_one c) hcf hcB hcC
  obtain ⟨hBT,hi⟩ := NaturalThreeAction.symmetric_three_sylow_extension T B hinv.1 dp.left_quotient
  have hBN : B ≤ Escape.H (T : Subgroup G) L R := dp.left_lt.le.trans
    (sup_le hPN (pCoreIn_le 2 _))
  have hstar := NaturalThreeAction.cubic_overgroup_mem_HStar h (B ⊔ (T : Subgroup G))
    le_sup_right (sup_le hBN h.sylow_normalizes_ZS) (fun hb => hBM (le_sup_left.trans hb)) hi
  exact ⟨B,C,dp,hBM,hinv.1,hinv.2,hstar,hBT,hi,c,hcL,hcTL,hcN,hc3,hcf,hcB,hcC⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
