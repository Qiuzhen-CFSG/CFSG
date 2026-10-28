module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFiveCubicParabolic
public import Theory.SpecificGroups.PSL3Two.Parabolics.TwoKernel
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# The two parabolics in the original binary-three cover

Lift the two maximal Sylow overgroups of the actual PSL3(2) model through
K/O2(K), where K = P O2(N_G(Z_S)) is the original invariant cover. Their
intersection is T intersect K and their join is K. Both literal two-core
quotients are S3, and each has index three over T intersect K. Since K
escapes M, order the pair so that its first member escapes M.

The full interval identifies the action of every element normalizing K
and T intersect K as a permutation of these two subgroups. The original
cubic normalizes that intersection by the natural line-centralizer
calculation; order three then makes it fix each parabolic. T permutes
the pair. This does not yet prove that T fixes either member: that step
requires the marked natural-action calculation of G.6.4(2a).

The final theorem retains the same W/Z_S action, factor, quotient maps,
and earlier S5 parabolic. Individual T-invariance, S5 escape and the
amalgam contradiction, initial 6.1.4–5 and the remaining geometry stay
with qt-d-1222-rankone-recognition-natural for unconditional 6.1.27.

Source: Aschbacher–Smith 6.1.19, printed p.675 (`refs/quasithin.pdf`).
The imported binary matrix model retains its ATLAS attribution in
`LICENSES/ATLAS.txt`.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeParabolic
open Matrix.PSL3Two
local notation "S3" => Equiv.Perm (Fin 3)

private theorem model_quotient (S : Sylow 2 PSL) (D : Subgroup PSL)
    (hD : IsCoatom D) (hSD : (S : Subgroup PSL) ≤ D) :
    Nonempty ((D ⧸ pCore 2 D) ≃* S3) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL borelSylow S
  let a := MulAut.conj g
  let e := a.mapSubgroup
  have hs : e Matrix.PSL3Two.borel = (S : Subgroup PSL) := by rw [←hg]; rfl
  have hb : Matrix.PSL3Two.borel ≤ e.symm D := by
    apply e.le_iff_le.mp
    simpa only [e.apply_symm_apply,hs] using hSD
  have hc : IsCoatom (e.symm D) := (e.symm.isCoatom_iff _).mpr hD
  have transport (U : Subgroup PSL) (he : e.symm D = U)
      (q : (U ⧸ pCore 2 U) ≃* S3) : Nonempty ((D ⧸ pCore 2 D) ≃* S3) := by
    have hUD : e U = D := by rw [←he,e.apply_symm_apply]
    let f : U ≃* D := (a.subgroupMap U).trans (MulEquiv.subgroupCongr hUD)
    exact ⟨(QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).symm.trans q⟩
  rcases (coatoms_over_borel _).mp ⟨hc,hb⟩ with hp | hl
  · exact transport _ hp pointParabolicCoreQuotientEquivS3
  · exact transport _ hl lineParabolicCoreQuotientEquivS3

private theorem lifted_quotient {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) (f : X →* PSL) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (D : Subgroup X) (hD : IsCoatom D)
    (hSD : (S : Subgroup X) ≤ D) : Nonempty ((D ⧸ pCore 2 D) ≃* S3) := by
  have hkD : f.ker ≤ D := (hk.le_sylow_of_normal S).trans hSD
  have hback : (D.map f).comap f = D := comap_map_eq_self hkD
  have hmap : IsCoatom (D.map f) := by
    refine ⟨?_,?_⟩
    · intro he
      exact hD.ne_top (by rw [←hback,he,comap_top])
    · intro U hU
      have hDU : D < U.comap f := lt_of_le_of_ne (map_le_iff_le_comap.mp hU.le) (by
        intro he
        exact hU.ne (by rw [he,map_comap_eq_self_of_surjective hf]))
      have he := congrArg (map f) (hD.2 _ hDU)
      simpa only [map_comap_eq_self_of_surjective hf,map_top_of_surjective f hf] using he
  obtain ⟨e⟩ := model_quotient (S.mapSurjective hf) (D.map f) hmap (map_mono hSD)
  have hker : IsPGroup 2 (f.subgroupMap D).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  exact ⟨((f.subgroupMap D).pCoreQuotientEquiv (f.subgroupMap_surjective D) hker).trans e⟩

private theorem quotient_pair {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) (e : (X ⧸ pCore 2 X) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) :
    ∃ B C : Subgroup X,
      IsCoatom B ∧ IsCoatom C ∧ B ≠ C ∧ B ⊓ C = (S : Subgroup X) ∧
      B ⊔ C = ⊤ ∧ (S : Subgroup X) < B ∧ (S : Subgroup X) < C ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* S3) ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* S3) ∧
      (∀ U : Subgroup X, (S : Subgroup X) ≤ U →
        U = (S : Subgroup X) ∨ U = B ∨ U = C ∨ U = ⊤) := by
  let q := (e.trans BinaryLinear.SmallParabolicLevi.linearThreeEquivProjective).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q :=
    (e.trans BinaryLinear.SmallParabolicLevi.linearThreeEquivProjective).surjective.comp
      (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _
      (e.trans BinaryLinear.SmallParabolicLevi.linearThreeEquivProjective).injective,
      QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨B,C,hB,hC,hne,hI,hSB,hSC,_,_,hall⟩ := two_kernel_parabolics S q hq hk
  exact ⟨B,C,hB,hC,hne,hI,hB.sup_eq_top_of_ne hC hne,hSB,hSC,
    lifted_quotient S q hq hk B hB hSB.le,lifted_quotient S q hq hk C hC hSC.le,hall⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeParabolic

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G]

/-- The two actual parabolics over the specified Sylow intersection. -/
structure NaturalThreeParabolicPair (S K B C : Subgroup G) : Prop where
  left_lt : B < K
  right_lt : C < K
  left_above : S < B
  right_above : S < C
  inf_eq : B ⊓ C = S
  sup_eq : B ⊔ C = K
  left_quotient : Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
  right_quotient : Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3))
  left_index : S.relIndex B = 3
  right_index : S.relIndex C = 3
  interval : ∀ U : Subgroup G, S ≤ U → U ≤ K →
    U = S ∨ U = B ∨ U = C ∨ U = K

namespace NaturalThreeParabolicPair
variable {S K B C : Subgroup G} (d : NaturalThreeParabolicPair S K B C)
include d

private theorem map_cases {c : G}
    (hcS : c ∈ normalizer (S : Set G)) (hcK : c ∈ normalizer (K : Set G)) :
    B.map (MulAut.conj c).toMonoidHom = B ∨ B.map (MulAut.conj c).toMonoidHom = C := by
  let e := (MulAut.conj c).mapSubgroup
  have hS : e S = S := mem_normalizer_iff_map_conj_eq.mp hcS
  have hK : e K = K := mem_normalizer_iff_map_conj_eq.mp hcK
  have hSB : S < e B := hS ▸ e.strictMono d.left_above
  have hBK : e B < K := hK ▸ e.strictMono d.left_lt
  rcases d.interval (e B) hSB.le hBK.le with hh | hh | hh | hh
  · exact (hSB.ne hh.symm).elim
  · exact Or.inl hh
  · exact Or.inr hh
  · exact (hBK.ne hh).elim

private theorem symm : NaturalThreeParabolicPair S K C B :=
  ⟨d.right_lt,d.left_lt,d.right_above,d.left_above,(by simpa only [inf_comm] using d.inf_eq),
    (by simpa only [sup_comm] using d.sup_eq),d.right_quotient,d.left_quotient,d.right_index,d.left_index,
    fun U hSU hUK => by
      rcases d.interval U hSU hUK with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))⟩

/-- Every element preserving the cover and its Sylow intersection permutes
the actual pair of parabolics. -/
theorem conjugate_cases {c : G}
    (hcS : c ∈ normalizer (S : Set G)) (hcK : c ∈ normalizer (K : Set G)) :
    (B.map (MulAut.conj c).toMonoidHom = B ∧ C.map (MulAut.conj c).toMonoidHom = C) ∨
    (B.map (MulAut.conj c).toMonoidHom = C ∧ C.map (MulAut.conj c).toMonoidHom = B) := by
  have hne : B ≠ C := by
    intro he
    have hh := d.inf_eq
    rw [he,inf_idem] at hh
    exact d.right_above.ne hh.symm
  have hi := map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
  rcases d.map_cases hcS hcK with hB | hB <;>
    rcases d.symm.map_cases hcS hcK with hC | hC
  · exact Or.inl ⟨hB,hC⟩
  · exact (hne (hi (hB.trans hC.symm))).elim
  · exact (hne (hi (hB.trans hC.symm))).elim
  · exact Or.inr ⟨hB,hC⟩

/-- An original cubic fixing the Sylow intersection fixes both parabolics. -/
theorem cubic_normalizes {c : G} (hc : c ^ 3 = 1)
    (hcS : c ∈ normalizer (S : Set G)) (hcK : c ∈ normalizer (K : Set G)) :
    c ∈ normalizer (B : Set G) ∧ c ∈ normalizer (C : Set G) := by
  rcases d.conjugate_cases hcS hcK with hfix | hswap
  · exact ⟨mem_normalizer_iff_map_conj_eq.mpr hfix.1,
      mem_normalizer_iff_map_conj_eq.mpr hfix.2⟩
  · let e := (MulAut.conj c).mapSubgroup
    have hcycle : e (e (e B)) = B := by
      change ((B.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c).toMonoidHom).map
        (MulAut.conj c).toMonoidHom = B
      rw [map_map,map_map]
      have he : ((MulAut.conj c).toMonoidHom.comp
          (MulAut.conj c).toMonoidHom).comp (MulAut.conj c).toMonoidHom = MonoidHom.id G := by
        have hh : (MulAut.conj c) ^ 3 = 1 := by rw [←map_pow,hc,map_one]
        exact congrArg (fun a : MulAut G => a.toMonoidHom) hh
      rw [he,map_id]
    change e B = C ∧ e C = B at hswap
    rw [hswap.1,hswap.2,hswap.1] at hcycle
    have hh := d.inf_eq
    rw [hcycle,inf_idem] at hh
    exact (d.left_above.ne hh.symm).elim

end NaturalThreeParabolicPair

namespace NaturalThreeParabolic
variable [Finite G]

private theorem ambient_pair (T : Sylow 2 G) (K : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) :
    ∃ B C : Subgroup G, NaturalThreeParabolicPair ((T : Subgroup G) ⊓ K) K B C := by
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  obtain ⟨D,E,hD,hE,hne,hI,hJ,hSD,hSE,⟨eD⟩,⟨eE⟩,hall⟩ := quotient_pair S e
  let B := D.map K.subtype
  let C := E.map K.subtype
  have hmapS : (S : Subgroup K).map K.subtype = (T : Subgroup G) ⊓ K := by
    rw [hS,subgroupOf_map_subtype]
  have hmaptop : (⊤ : Subgroup K).map K.subtype = K := by
    rw [←MonoidHom.range_eq_map,range_subtype]
  have map_lt {U V : Subgroup K} (hUV : U < V) : U.map K.subtype < V.map K.subtype :=
    lt_of_le_of_ne (map_mono hUV.le) (fun he => hUV.ne (map_injective K.subtype_injective he))
  have hBK : B < K := hmaptop ▸ map_lt hD.lt_top
  have hCK : C < K := hmaptop ▸ map_lt hE.lt_top
  let b := D.equivMapOfInjective K.subtype K.subtype_injective
  let c := E.equivMapOfInjective K.subtype K.subtype_injective
  refine ⟨B,C,hBK,hCK,hmapS ▸ map_lt hSD,hmapS ▸ map_lt hSE,?_,?_,
    ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans eD⟩,
    ⟨(QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).symm.trans eE⟩,?_,?_,?_⟩
  · rw [←map_inf _ _ _ K.subtype_injective,hI,hmapS]
  · rw [←Subgroup.map_sup,hJ,hmaptop]
  · rw [←hmapS,relIndex_map_map_of_injective _ _ K.subtype_injective]
    exact SymmetricThreeTwoCore.sylow_index_three eD (S.subtype hSD.le)
  · rw [←hmapS,relIndex_map_map_of_injective _ _ K.subtype_injective]
    exact SymmetricThreeTwoCore.sylow_index_three eE (S.subtype hSE.le)
  · intro U hSU hUK
    have hSU' : (S : Subgroup K) ≤ U.subgroupOf K := by
      rw [hS]
      exact fun x hx => hSU ⟨hx,x.property⟩
    have hUmap : (U.subgroupOf K).map K.subtype = U := map_subgroupOf_eq_of_le hUK
    rcases hall (U.subgroupOf K) hSU' with h | h | h | h
    · exact Or.inl (by rw [←hUmap,h,hmapS])
    · exact Or.inr (Or.inl (by rw [←hUmap,h]))
    · exact Or.inr (Or.inr (Or.inl (by rw [←hUmap,h])))
    · exact Or.inr (Or.inr (Or.inr (by rw [←hUmap,h,hmaptop])))

end NaturalThreeParabolic
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}

/-- The original L3(2) cover has two actual parabolics, permuted by T and
fixed individually by the original cubic, with the first one escaping M. -/
@[expose] def NaturalThreeCubicParabolicData
    (T : Sylow 2 G) (L R P N M : Subgroup G) : Prop :=
  Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) →
    let K := P ⊔ N.pCoreIn 2
    ∃ B C : Subgroup G, NaturalThreeParabolicPair ((T : Subgroup G) ⊓ K) K B C ∧
      (¬ B ≤ M) ∧
      (∀ t ∈ (T : Subgroup G),
        (B.map (MulAut.conj t).toMonoidHom = B ∧ C.map (MulAut.conj t).toMonoidHom = C) ∨
        (B.map (MulAut.conj t).toMonoidHom = C ∧ C.map (MulAut.conj t).toMonoidHom = B)) ∧
      ∃ c ∈ L, c ∈ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
        c ∈ N ∧ orderOf c = 3 ∧
        (∀ z ∈ ZS (T : Subgroup G) L R, c * z * c⁻¹ = z → z = 1) ∧
        c ∈ normalizer (B : Set G) ∧ c ∈ normalizer (C : Set G)

/-- Construct the escaping L3(2) parabolic pair on the original invariant
cover, retaining the cubic and its action on the original central line. -/
theorem natural_three_cubic_parabolic_of_invariant_cover
    {X : Type*} [Group X]
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (P : Subgroup G) (σ : Escape.I (T : Subgroup G) L R →* MulAut X)
    (hPI : P ≤ Escape.I (T : Subgroup G) L R)
    (hc : NaturalInvariantCoverData T P (Escape.I (T : Subgroup G) L R)
      (Escape.H (T : Subgroup G) L R) σ hPI)
    (hescape : NaturalEscapingCoverData T P (Escape.H (T : Subgroup G) L R) M) :
    NaturalThreeCubicParabolicData T L R P (Escape.H (T : Subgroup G) L R) M := by
  rintro ⟨eP⟩
  let K := P ⊔ (Escape.H (T : Subgroup G) L R).pCoreIn 2
  obtain ⟨hKI,hNK,hTK,_,⟨eK⟩,_⟩ := hc
  obtain ⟨B,C,d⟩ := NaturalThreeParabolic.ambient_pair T K hTK (eK.trans eP)
  have hKout : ¬ K ≤ M := hescape.2.1
  have hex : ∃ B C : Subgroup G,
      NaturalThreeParabolicPair ((T : Subgroup G) ⊓ K) K B C ∧ ¬ B ≤ M := by
    by_cases hBM : B ≤ M
    · exact ⟨C,B,d.symm,fun hCM => hKout (d.sup_eq ▸ sup_le hBM hCM)⟩
    · exact ⟨B,C,d,hBM⟩
  obtain ⟨B,C,d,hBM⟩ := hex
  have ht (t : G) (ht : t ∈ (T : Subgroup G)) :
      t ∈ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨(T : Subgroup G).le_normalizer ht,hTK ht⟩
  obtain ⟨c,hcL,hcTL,hcN,hc3,hcf⟩ := natural_four_exists_cubic h hnat
  have hS : (T : Subgroup G) ⊓ K =
      ((T : Subgroup G) ⊓ centralizer (ZS (T : Subgroup G) L R : Set G)) ⊓ K := by
    rw [inf_assoc,inf_eq_right.mpr (show K ≤ centralizer (ZS (T : Subgroup G) L R : Set G) from hKI)]
  have hcS : c ∈ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
    rw [hS]
    exact inf_normalizer_le_normalizer_inf
      ⟨natural_cubic_normalizes_line_sylow h hnat hcL hcN,hNK hcN⟩
  have hcPow : c ^ 3 = 1 := hc3 ▸ pow_orderOf_eq_one c
  exact ⟨B,C,d,hBM,fun t ht' => d.conjugate_cases (ht t ht') (hTK ht'),
    c,hcL,hcTL,hcN,hc3,hcf,d.cubic_normalizes hcPow hcS (hNK hcN)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d
/-- The original W/Z_S witness with the two L3(2) parabolics, one escaping M,
both fixed by the original cubic and permuted by T. -/
theorem exists_ambient_three_cubic_parabolic
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
            NaturalThreeCubicParabolicData T L R P N M := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive⟩ :=
    d.exists_ambient_five_cubic_parabolic h hnat hE hs hNS hab
  let := hZ
  let := hX
  exact ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,
    natural_three_cubic_parabolic_of_invariant_cover (hn ▸ h) (hn ▸ hnat) _ σ hPI hcover hescape⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
