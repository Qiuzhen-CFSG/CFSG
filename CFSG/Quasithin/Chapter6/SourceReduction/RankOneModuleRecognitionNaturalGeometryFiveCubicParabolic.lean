module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFiveParabolic
public import Theory.SpecificGroups.SL2.NaturalStabilizer
/-!
# The source cubic preserves the canonical S5 parabolic

The stabilizer of a nonzero natural vector is a two-group. Applied through
the literal L/O2(L) model, this makes C_L(Z_S) a two-group. Since LT/L is
also a two-group, C_{LT}(Z_S) is exactly C_T(Z_S). Thus the whole line
normalizer in L preserves this Sylow intersection, although its cubic need
not normalize T. Intersecting with the original invariant cover K and using
uniqueness of the S5 parabolic proves invariance under T and N_L(Z_S).

The final theorem keeps the original W/Z_S action, factor and quotient maps.
It constructs a cubic in the original L with its fixed-free line action and
proves that it preserves this same parabolic. No stronger invariance of P
or of W under the cubic is used. Parabolic escape, the L3(2) row and the
amalgam contradiction, initial 6.1.4–5 and the remaining geometry stay with
qt-d-1222-rankone-recognition-natural for unconditional 6.1.27 assembly.

Source: Aschbacher–Smith 6.1.19, printed p.675 (`refs/quasithin.pdf`).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

private theorem line_centralizer_in_L_two
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n) :
    IsPGroup 2 (L ⊓ centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) := by
  obtain ⟨z₀,hz₀⟩ := ne_bot_iff_exists_ne_one.mp h.ZS_ne_bot
  let z : G := z₀
  have hz : z ∈ ZS (T : Subgroup G) L R := z₀.property
  have hz1 : z ≠ 1 := fun he => hz₀ (Subtype.ext he)
  obtain ⟨F,_,_,_,hF,e,f,hf⟩ := hnat
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let v := (f ⟨z,hz.1⟩).toAdd
  have hv : v ≠ 0 := by
    intro hv
    have hh : f ⟨z,hz.1⟩ = 1 := congrArg Multiplicative.ofAdd hv
    exact hz1 (congrArg Subtype.val (f.injective (hh.trans (map_one f).symm)))
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hp := (Matrix.SL2.stabilizer_nonzero_isPGroup v hv).comap_of_ker_isPGroup q hk
  have hsub : (centralizer (ZS (T : Subgroup G) L R : Set G)).subgroupOf L ≤
      (MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 2) F) v).comap q := by
    intro x hx
    change (q x).val.mulVec v = v
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    have hh := hf x ⟨z,hz.1⟩
    have hc : (x : G) * z * (x : G)⁻¹ = z :=
      mul_inv_eq_iff_eq_mul.mpr (hx z hz).symm
    simpa [Representation.specialLinearNatural_apply,q,v] using hh.trans hc
  have hh := (hp.to_le hsub).map L.subtype
  rwa [subgroupOf_map_subtype,inf_comm] at hh

/-- The local line centralizer lies in the original Sylow. -/
theorem natural_local_line_centralizer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer (ZS (T : Subgroup G) L R : Set G) =
      (T : Subgroup G) ⊓ centralizer (ZS (T : Subgroup G) L R : Set G) := by
  let H := L ⊔ (T : Subgroup G)
  let I := centralizer (ZS (T : Subgroup G) L R : Set G)
  let C := H ⊓ I
  let A := L.subgroupOf H
  let U := (T : Subgroup G).subgroupOf H
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer h.sylow_normalizes_L)
  have hgen : A ⊔ U = ⊤ := by
    rw [←subgroupOf_sup (show L ≤ H from le_sup_left)
      (show (T : Subgroup G) ≤ H from le_sup_right),subgroupOf_self]
  have hquot : IsPGroup 2 (H ⧸ A) := isPGroup_quotient_of_sup_eq_top A U
    T.isPGroup'.comap_subtype hgen
  let f : C →* H ⧸ A := (QuotientGroup.mk' A).comp (inclusion inf_le_left)
  have hk : IsPGroup 2 f.ker := by
    apply (line_centralizer_in_L_two h hnat).comap_subtype.to_le
    intro x hx
    have hxA : (inclusion (show C ≤ H from inf_le_left)) x ∈ A :=
      (QuotientGroup.eq_one_iff _).mp hx
    exact ⟨hxA,x.property.2⟩
  have hC : IsPGroup 2 C := by
    have hp := (hquot.to_subgroup (⊤ : Subgroup (H ⧸ A))).comap_of_ker_isPGroup f hk
    rw [comap_top] at hp
    exact hp.of_equiv Subgroup.topEquiv
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T I
    (h.sylow_normalizes_ZS.trans (normalizer_le_normalizer_centralizer _))
  have he : C.subgroupOf I = (S : Subgroup I) := S.is_maximal' hC.comap_subtype (by
    rw [hS]
    exact fun x hx => ⟨(show (T : Subgroup G) ≤ H from le_sup_right) hx,x.property⟩)
  have hh := congrArg (map I.subtype) he
  rw [map_subgroupOf_eq_of_le (show C ≤ I from inf_le_right),hS,subgroupOf_map_subtype] at hh
  exact hh

/-- The source cubic preserves the line-centralizing Sylow intersection. -/
theorem natural_cubic_normalizes_line_sylow
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    {c : G} (hcL : c ∈ L) (hcN : c ∈ normalizer (ZS (T : Subgroup G) L R : Set G)) :
    c ∈ normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) := by
  rw [←natural_local_line_centralizer h hnat]
  exact inf_normalizer_le_normalizer_inf
    ⟨(L ⊔ (T : Subgroup G)).le_normalizer ((show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) hcL),
      normalizer_le_normalizer_centralizer _ hcN⟩

private theorem parabolic_fixed_of_unique
    (S K B : Subgroup G) (hBK : B < K) (hSB : S ≤ B)
    (hmax : ∀ C : Subgroup G, S ≤ C → C < K → C ≤ B)
    {c : G} (hcS : c ∈ normalizer (S : Set G))
    (hcK : c ∈ normalizer (K : Set G)) :
    c ∈ normalizer (B : Set G) := by
  let f := (MulAut.conj c).toMonoidHom
  have hf := (MulAut.conj c).injective
  have hK : K.map f = K := mem_normalizer_iff_map_conj_eq.mp hcK
  have hS : S.map f = S := mem_normalizer_iff_map_conj_eq.mp hcS
  have hBC : B.map f < K := lt_of_le_of_ne (hK ▸ map_mono hBK.le)
    (fun he => hBK.ne (map_injective hf (he.trans hK.symm)))
  have hSBC : S ≤ B.map f := hS ▸ map_mono hSB
  exact mem_normalizer_iff_map_conj_eq.mpr (eq_of_le_of_card_ge
    (hmax _ hSBC hBC) (card_map_of_injective (K := B) (f := f) hf).ge)

/-- Every original local line-normalizing element preserves the canonical
S5 parabolic. In particular this applies to the source cubic without
assuming that it normalizes T. -/
theorem natural_five_parabolic_cubic_invariant
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (K B : Subgroup G)
    (hKI : K ≤ centralizer (ZS (T : Subgroup G) L R : Set G))
    (hNK : normalizer (ZS (T : Subgroup G) L R : Set G) ≤ normalizer (K : Set G))
    (hBK : B < K) (hSB : (T : Subgroup G) ⊓ K ≤ B)
    (hmax : ∀ C : Subgroup G, (T : Subgroup G) ⊓ K ≤ C → C < K → C ≤ B) :
    L ⊓ normalizer (ZS (T : Subgroup G) L R : Set G) ≤ normalizer (B : Set G) := by
  intro c hc
  apply parabolic_fixed_of_unique ((T : Subgroup G) ⊓ K) K B hBK hSB hmax
    (hcK := hNK hc.2)
  have he : (T : Subgroup G) ⊓ K =
      ((T : Subgroup G) ⊓ centralizer (ZS (T : Subgroup G) L R : Set G)) ⊓ K := by
    rw [inf_assoc,inf_eq_right.mpr hKI]
  rw [he]
  exact inf_normalizer_le_normalizer_inf
    ⟨natural_cubic_normalizes_line_sylow h hnat hc.1 hc.2,hNK hc.2⟩

/-- The canonical S5 parabolic is invariant under the original Sylow and
the entire line normalizer in L. The cubic remains an element of the original
L and retains its fixed-free action on the original line. -/
@[expose] def NaturalFiveCubicParabolicData (T : Sylow 2 G) (L R P N : Subgroup G) : Prop :=
  Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5)) →
    let K := P ⊔ N.pCoreIn 2
    ∃ B : Subgroup G, B < K ∧ (T : Subgroup G) ⊓ K ≤ B ∧
      N ⊓ normalizer (T : Set G) ≤ normalizer (B : Set G) ∧
      (T : Subgroup G) ⊔ (L ⊓ N) ≤ normalizer (B : Set G) ∧
      (∃ c ∈ L, c ∈ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
        c ∈ N ∧ orderOf c = 3 ∧
        (∀ z ∈ ZS (T : Subgroup G) L R, c * z * c⁻¹ = z → z = 1) ∧
        c ∈ normalizer (B : Set G)) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
      (∀ C : Subgroup G, (T : Subgroup G) ⊓ K ≤ C → C < K → C ≤ B) ∧
      Nonempty (((B ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (B ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      (T : Subgroup G).relIndex (B ⊔ (T : Subgroup G)) = 3

/-- Apply the line-centralizer calculation to the canonical parabolic in the
same original invariant cover. This discharges the cubic-invariance step
without requiring normalization of T by the cubic or of P by T. -/
theorem natural_five_cubic_parabolic_of_invariant_cover
    {X : Type*} [Group X]
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (P : Subgroup G) (σ : Escape.I (T : Subgroup G) L R →* MulAut X)
    (hPI : P ≤ Escape.I (T : Subgroup G) L R)
    (hc : NaturalInvariantCoverData T P (Escape.I (T : Subgroup G) L R)
      (Escape.H (T : Subgroup G) L R) σ hPI) :
    NaturalFiveCubicParabolicData T L R P (Escape.H (T : Subgroup G) L R) := by
  intro he
  obtain ⟨B,hBK,hSB,hNB,hTB,eB,hmax,eBT,hi⟩ :=
    natural_five_parabolic_of_invariant_cover T P _ _ σ hPI hc he
  obtain ⟨hKI,hNK,_⟩ := hc
  have hLB := natural_five_parabolic_cubic_invariant h hnat _ B hKI hNK hBK hSB hmax
  obtain ⟨c,hcL,hcTL,hcN,hc3,hcf⟩ := natural_four_exists_cubic h hnat
  exact ⟨B,hBK,hSB,hNB,sup_le hTB hLB,
    ⟨c,hcL,hcTL,hcN,hc3,hcf,hLB ⟨hcL,hcN⟩⟩,eB,hmax,eBT,hi⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d
/-- The original W/Z_S witness with a canonical S5 parabolic preserved
by T and the line normalizer in L, including the original cubic. -/
theorem exists_ambient_five_cubic_parabolic
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
            NaturalFiveCubicParabolicData T L R P N := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape⟩ :=
    d.exists_ambient_escaping_cover h hnat hE hs hNS hab
  let := hZ
  let := hX
  exact ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,
    natural_five_cubic_parabolic_of_invariant_cover (hn ▸ h) (hn ▸ hnat) _ σ hPI hcover⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
