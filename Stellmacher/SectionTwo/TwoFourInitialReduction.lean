module

public import Stellmacher.SectionTwo.LemmaTwoThree
public import Stellmacher.BaumannIntermediate
public import Stellmacher.BaumannNormalizer
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.OmegaOneCenterMap

/-!
# The initial reduction in Stellmacher (2.4)

This module packages the first reduction in Stellmacher (2.4), Journal of
Algebra 190 (1997), p. 20.  Under the hypothesis that no nontrivial
characteristic subgroup of the Sylow 2-subgroup `S` is normal in `G`, neither
the central omega subgroup nor the Baumann subgroup can become normal.  The
unique maximal overgroup hypothesis and the Frattini argument then identify
`O₂(G)` with `C_S(V)`.  The centralizing case for `V` would make the
Baumann subgroup normal, so `V` does not centralize `J(S)`.

The theorem also returns an intrinsic characteristic nontrivial subgroup of
`S` whose ambient image is the Baumann subgroup.  That datum is needed to
transport characteristic rigidity to the chosen local subgroup later in
(2.4).  Center and automorphism calculations are kept private.
-/

open scoped Pointwise

namespace Stellmacher.SectionTwo

universe u

private theorem le_unique_maximal_ambient
    {G : Type u} [Group G] [Finite G]
    {S L : Subgroup G} {M : Subgroup (⊤ : Subgroup G)}
    (huniq : ∀ M' : Subgroup (⊤ : Subgroup G), IsCoatom M' →
      S ≤ M'.map (⊤ : Subgroup G).subtype → M' = M)
    (hSL : S ≤ L) (hLne : L ≠ ⊤) :
    L ≤ M.map (⊤ : Subgroup G).subtype := by
  let _ : Finite (⊤ : Subgroup G) := Subtype.finite
  have hLsub_ne : L.subgroupOf (⊤ : Subgroup G) ≠ ⊤ := by
    intro htop
    apply hLne
    rw [← Subgroup.map_subgroupOf_eq_of_le
      (show L ≤ (⊤ : Subgroup G) from le_top), htop,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨M', hM'coat, hLM'⟩ :=
    (eq_top_or_exists_le_coatom (L.subgroupOf (⊤ : Subgroup G))).resolve_left hLsub_ne
  have hSM' : S ≤ M'.map (⊤ : Subgroup G).subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le
      (show L ≤ (⊤ : Subgroup G) from le_top)] at hSL
    exact hSL.trans (Subgroup.map_mono hLM')
  rw [← huniq M' hM'coat hSM']
  rw [← Subgroup.map_subgroupOf_eq_of_le
    (show L ≤ (⊤ : Subgroup G) from le_top)]
  exact Subgroup.map_mono hLM'

private theorem zSubgroup_internal_data
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G) :
    ∃ ZS : Subgroup S,
      ZS.Characteristic ∧ ZS ≠ ⊥ ∧
      ZS.map (S : Subgroup G).subtype = zSubgroup S := by
  let C : Subgroup S := Subgroup.center (S : Subgroup G)
  let W : Subgroup C := omega₁ (G := C) (p := 2)
  let ZS : Subgroup S := W.map C.subtype
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSne : (S : Subgroup G) ≠ ⊥ :=
    S.ne_bot_of_dvd_card (even_iff_two_dvd.mp h.even_order)
  let _ : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot _).mpr hSne
  have hCne : C ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot C).mp S.isPGroup'.center_nontrivial
  have hCp : IsPGroup 2 C := S.isPGroup'.to_subgroup C
  obtain ⟨n, hn, hcard⟩ := hCp.nontrivial_iff_card.mp
    ((Subgroup.nontrivial_iff_ne_bot C).mpr hCne)
  have htwo : 2 ∣ Nat.card C := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  have hZSne : ZS ≠ ⊥ := omega₁_map_subtype_ne_bot C 2 htwo
  have hZSchar : ZS.Characteristic := by
    let _ : C.Characteristic := Subgroup.centerCharacteristic
    let _ : W.Characteristic := omega₁_characteristic C
    exact Subgroup.characteristic_of_characteristic_of_characteristic
  exact ⟨ZS, hZSchar, hZSne, rfl⟩

private theorem two_four_core_eq_centralizer
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hcharacteristic :
      ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
        ¬ (K.map (S : Subgroup G).subtype).Normal)
    (hunique :
      IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G)) :
    pCore 2 G =
      (S : Subgroup G) ⊓ Subgroup.centralizer (vSubgroup S : Set G) := by
  classical
  let V := vSubgroup S
  let Z := zSubgroup S
  let C := Subgroup.centralizer (V : Set G)
  let R := (S : Subgroup G) ⊓ C
  have hVnormal : V.Normal := by
    dsimp [V, vSubgroup]
    infer_instance
  let _ : V.Normal := hVnormal
  have hCnormal : C.Normal := by
    dsimp [C]
    infer_instance
  let _ : C.Normal := hCnormal
  have hQleS : pCore 2 G ≤ (S : Subgroup G) := fitting_pCore_le_sylow S
  have hZleV : Z ≤ V := Subgroup.le_normalClosure
  have hZcentQ : Z ≤ Subgroup.centralizer (pCore 2 G : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    simp only [Z, zSubgroup, omegaOneCenterAmbient] at hz
    obtain ⟨zS, hzS, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨zC, _hzOmega, rfl⟩ := Subgroup.mem_map.mp hzS
    have hqS : q ∈ (S : Subgroup G) := hQleS hq
    exact congrArg (fun x : S ↦ (x : G))
      ((Subgroup.mem_center_iff.mp zC.property) ⟨q, hqS⟩)
  have hVcentQ : V ≤ Subgroup.centralizer (pCore 2 G : Set G) :=
    Subgroup.normalClosure_le_normal hZcentQ
  have hQleC : pCore 2 G ≤ C := Subgroup.le_centralizer_iff.mp hVcentQ
  have hQleR : pCore 2 G ≤ R := le_inf hQleS hQleC
  obtain ⟨ZS, hZSchar, hZSne, hZSmap⟩ := zSubgroup_internal_data h S
  have hZnotNormal : ¬ Z.Normal := by
    dsimp [Z]
    rw [← hZSmap]
    exact hcharacteristic ZS hZSchar hZSne
  have hCnormZ : C ≤ Subgroup.normalizer (Z : Set G) :=
    (Subgroup.centralizer_le hZleV).trans
      (Subgroup.centralizer_le_normalizer (Z : Set G))
  have hZleS : Z ≤ (S : Subgroup G) := by
    dsimp [Z, zSubgroup, omegaOneCenterAmbient]
    exact Subgroup.map_subtype_le _
  have hZsub : Z.subgroupOf (S : Subgroup G) = ZS := by
    apply Subgroup.map_injective (f := (S : Subgroup G).subtype)
      (S : Subgroup G).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hZleS, hZSmap]
  have hSnormZ : (S : Subgroup G) ≤ Subgroup.normalizer (Z : Set G) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hZleS).mp
    rw [hZsub]
    let _ : ZS.Characteristic := hZSchar
    exact Subgroup.normal_of_characteristic ZS
  have hCSproper : C ⊔ (S : Subgroup G) ≠ ⊤ := by
    intro htop
    apply hZnotNormal
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← htop]
    exact sup_le hCnormZ hSnormZ
  obtain ⟨M, hMcoat, hSM, hMuniq⟩ := hunique
  have hCSleM : C ⊔ (S : Subgroup G) ≤
      M.map (⊤ : Subgroup G).subtype :=
    le_unique_maximal_ambient hMuniq le_sup_right hCSproper
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal C
  have hTR : (T : Subgroup C).map C.subtype = R := by
    rw [hT, Subgroup.subgroupOf_map_subtype]
  let N := Subgroup.normalizer (R : Set G)
  have hSleN : (S : Subgroup G) ≤ N := by
    change (S : Subgroup G) ≤
      Subgroup.normalizer (((S : Subgroup G) ⊓ C : Subgroup G) : Set G)
    exact (le_inf (show (S : Subgroup G) ≤
        Subgroup.normalizer ((S : Subgroup G) : Set G) from Subgroup.le_normalizer)
      (Subgroup.le_normalizer_of_normal (H := C))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hfrattini : N ⊔ C = ⊤ := by
    simpa only [N, hTR] using T.normalizer_sup_eq_top
  have hNtop : N = ⊤ := by
    by_contra hNne
    have hNleM : N ≤ M.map (⊤ : Subgroup G).subtype :=
      le_unique_maximal_ambient hMuniq hSleN hNne
    have htopLe : (⊤ : Subgroup G) ≤ M.map (⊤ : Subgroup G).subtype := by
      have hsup : N ⊔ C ≤ M.map (⊤ : Subgroup G).subtype :=
        sup_le hNleM (le_sup_left.trans hCSleM)
      simpa only [hfrattini] using hsup
    have hMmapTop : M.map (⊤ : Subgroup G).subtype = ⊤ := top_unique htopLe
    apply hMcoat.ne_top
    apply Subgroup.map_injective (f := (⊤ : Subgroup G).subtype)
      (⊤ : Subgroup G).subtype_injective
    rw [hMmapTop, Subgroup.map_top_of_surjective]
    intro g
    exact ⟨⟨g, trivial⟩, rfl⟩
  have hRnormal : R.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  have hRp : IsPGroup 2 R := S.isPGroup'.to_le inf_le_left
  have hRleQ : R ≤ pCore 2 G := le_sSup ⟨hRnormal, hRp⟩
  exact le_antisymm hQleR hRleQ

private theorem centralizer_map_equiv
    {G : Type u} [Group G] (A : Subgroup G) (e : G ≃* G) :
    (Subgroup.centralizer (A : Set G)).map e.toMonoidHom =
      Subgroup.centralizer (A.map e.toMonoidHom : Set G) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x ∈ Subgroup.centralizer (A : Set G) at hx
    change e x ∈ Subgroup.centralizer (A.map e.toMonoidHom : Set G)
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    rintro _ ⟨a, ha, rfl⟩
    simpa using congrArg e.toMonoidHom (hx a ha)
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    change y ∈ Subgroup.centralizer (A.map e.toMonoidHom : Set G) at hy
    change e.symm y ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro a ha
    apply e.injective
    simpa using hy (e a) ⟨a, ha, rfl⟩

private theorem baumann_internal_data
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G) :
    let B := (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient
        (elementaryAbelianMaxJ (S : Subgroup G)) : Set G)
    ∃ BS : Subgroup S,
      BS.Characteristic ∧ BS ≠ ⊥ ∧
      BS.map (S : Subgroup G).subtype = B := by
  classical
  let f : S →* G := (S : Subgroup G).subtype
  let J : Subgroup S := elementaryAbelianMaxJ (⊤ : Subgroup S)
  let W : Subgroup S := omegaOneCenterAmbient J
  let BS : Subgroup S :=
    (⊤ : Subgroup S) ⊓ Subgroup.centralizer (W : Set S)
  let B := (S : Subgroup G) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient
      (elementaryAbelianMaxJ (S : Subgroup G)) : Set G)
  have htop : (⊤ : Subgroup S).map f = (S : Subgroup G) :=
    (MonoidHom.range_eq_map f).symm.trans
      (Subgroup.range_subtype (S : Subgroup G))
  have hJmap : J.map f = elementaryAbelianMaxJ (S : Subgroup G) := by
    calc
      J.map f = elementaryAbelianMaxJ ((⊤ : Subgroup S).map f) :=
        (elementaryAbelianMaxJ_map_injective f
          (S : Subgroup G).subtype_injective (⊤ : Subgroup S)).symm
      _ = elementaryAbelianMaxJ (S : Subgroup G) := by rw [htop]
  have hWmap : W.map f =
      omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) := by
    rw [← hJmap]
    exact (omegaOneCenterAmbient_map_injective f
      (S : Subgroup G).subtype_injective J).symm
  have hBSmap : BS.map f = B := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨b.property, ?_⟩
      change f b ∈ Subgroup.centralizer
        (omegaOneCenterAmbient
          (elementaryAbelianMaxJ (S : Subgroup G)) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : y ∈ W.map f := by rw [hWmap]; exact hy
      obtain ⟨w, hw, rfl⟩ := hy'
      exact congrArg f (Subgroup.mem_centralizer_iff.mp hb.2 w hw)
    · intro hx
      obtain ⟨s, hs⟩ : ∃ s : S, f s = x := ⟨⟨x, hx.1⟩, rfl⟩
      refine ⟨s, ⟨trivial, ?_⟩, hs⟩
      change s ∈ Subgroup.centralizer (W : Set S)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      apply (S : Subgroup G).subtype_injective
      change (w : G) * f s = f s * (w : G)
      rw [hs]
      exact Subgroup.mem_centralizer_iff.mp hx.2 (f w)
        (by rw [← hWmap]; exact ⟨w, hw, rfl⟩)
  have hBSchar : BS.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro e
    dsimp only [BS]
    rw [Subgroup.map_inf _ _ _ e.injective, centralizer_map_equiv]
    have htopE : (⊤ : Subgroup S).map e.toMonoidHom = ⊤ := by simp
    have hJE : J.map e.toMonoidHom = J := by
      calc
        J.map e.toMonoidHom =
            elementaryAbelianMaxJ ((⊤ : Subgroup S).map e.toMonoidHom) :=
          (elementaryAbelianMaxJ_map_equiv e (⊤ : Subgroup S)).symm
        _ = J := by rw [htopE]
    have hWE : W.map e.toMonoidHom = W := by
      calc
        W.map e.toMonoidHom = omegaOneCenterAmbient (J.map e.toMonoidHom) :=
          (omegaOneCenterAmbient_map_injective e.toMonoidHom e.injective J).symm
        _ = W := by rw [hJE]
    rw [htopE, hWE]
  have hBSne : BS ≠ ⊥ := by
    obtain ⟨ZS, _hZSchar, hZSne, hZSmap⟩ := zSubgroup_internal_data h S
    have hZleB : zSubgroup S ≤ B := by
      intro z hz
      refine ⟨?_, ?_⟩
      · dsimp [zSubgroup, omegaOneCenterAmbient] at hz
        obtain ⟨zS, _hz, rfl⟩ := Subgroup.mem_map.mp hz
        exact zS.property
      · change z ∈ Subgroup.centralizer
          (omegaOneCenterAmbient
            (elementaryAbelianMaxJ (S : Subgroup G)) : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hwS : w ∈ (S : Subgroup G) :=
          ((Subgroup.map_subtype_le _).trans
            (sSup_le fun _ hA => hA.1)) hw
        exact (mem_omegaOneCenterAmbient_iff _ _).mp hz |>.2.2 w hwS
    intro hbot
    have hBbot : B = ⊥ := by
      rw [← hBSmap, hbot, Subgroup.map_bot]
    have hZbot : zSubgroup S = ⊥ :=
      le_bot_iff.mp (hZleB.trans_eq hBbot)
    apply hZSne
    apply Subgroup.map_injective (S : Subgroup G).subtype_injective
    rw [hZSmap, hZbot, Subgroup.map_bot]
  exact ⟨BS, hBSchar, hBSne, hBSmap⟩

private theorem two_four_noncentral
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hcharacteristic :
      ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
        ¬ (K.map (S : Subgroup G).subtype).Normal)
    (hunique :
      IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G)) :
    ¬ vSubgroup S ≤
      Subgroup.centralizer
        (elementaryAbelianMaxJ (S : Subgroup G) : Set G) := by
  intro hcent
  let B := (S : Subgroup G) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient
      (elementaryAbelianMaxJ (S : Subgroup G)) : Set G)
  have hcore := two_four_core_eq_centralizer h S hcharacteristic hunique
  obtain ⟨hVcore, hVe⟩ := vSubgroup_le_twoCore_and_elementaryAbelian h S
  let _ : IsElementaryAbelian 2 (vSubgroup S) := hVe
  have hVZ := elementary_centralizer_maxJ_le_omegaCenter
    (S : Subgroup G) (vSubgroup S)
    (hVcore.trans (fitting_pCore_le_sylow S)) hcent
  have hBcore : B ≤ pCore 2 G := by
    rw [hcore]
    exact inf_le_inf_left _ (Subgroup.centralizer_le hVZ)
  have hBcoreEq : B = pCore 2 G ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient
        (elementaryAbelianMaxJ (pCore 2 G)) : Set G) := by
    dsimp [B] at hBcore ⊢
    exact (baumann_eq_of_intermediate (S : Subgroup G) (pCore 2 G)
      hBcore (fitting_pCore_le_sylow S)).symm
  have hBnormal : B.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [hBcoreEq]
    exact (show (⊤ : Subgroup G) ≤
        Subgroup.normalizer (pCore 2 G : Set G) by
      rw [Subgroup.normalizer_eq_top]).trans
        (normalizer_le_normalizer_baumann _)
  obtain ⟨BS, hBSchar, hBSne, hBSmap⟩ := baumann_internal_data h S
  exact (hcharacteristic BS hBSchar hBSne) (hBSmap ▸ hBnormal)

/-- The core-centralizer equality, noncentrality, and intrinsic Baumann data
needed to start the local argument in Stellmacher (2.4). -/
public theorem two_four_initial_reduction
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hcharacteristic :
      ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
        ¬ (K.map (S : Subgroup G).subtype).Normal)
    (hunique :
      IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G)) :
    let B := (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient
        (elementaryAbelianMaxJ (S : Subgroup G)) : Set G)
    pCore 2 G =
        (S : Subgroup G) ⊓ Subgroup.centralizer (vSubgroup S : Set G) ∧
      ¬ vSubgroup S ≤
        Subgroup.centralizer
          (elementaryAbelianMaxJ (S : Subgroup G) : Set G) ∧
      ∃ BS : Subgroup S,
        BS.Characteristic ∧ BS ≠ ⊥ ∧
        BS.map (S : Subgroup G).subtype = B := by
  dsimp only
  exact ⟨two_four_core_eq_centralizer h S hcharacteristic hunique,
    two_four_noncentral h S hcharacteristic hunique,
    baumann_internal_data h S⟩

end Stellmacher.SectionTwo
