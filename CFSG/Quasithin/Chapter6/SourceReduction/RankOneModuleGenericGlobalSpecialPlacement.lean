module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2RootPair
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityRootPair
public import Theory.GroupTheory.PGroup.NormalizedSylowConjugation
public import Theory.Frattini.Intersection
public import Theory.Frattini.SquareImage
public import Theory.SpecificGroups.SL2.SylowConsequences

/-!
# Sylow placements of the special-core root pair

For the actual G₂ and triality comparisons, S lies in K = O²(H), and
K/O₂(K) is binary PSL₂. Its two-subgroups have exponent two. Therefore
Φ(S) ≤ Q = O₂(K). This supplies the precise Frattini consequence used
in F.4.35; abelianness of an arbitrary quotient alone would not suffice.

Write Z = Z(K). If U ≤ Q centralizes Z^g and Φ(U) = Z, Sylow conjugacy
inside C_G(Z) puts U in S^{g'} while leaving Z^{g'} = Z^g. Frattini
functoriality then gives Z ≤ Q^{g'}. A second conjugation in C_G(Z)
places C_{Q^{g'}}(Z) in S. It preserves Q and Z, but changes the marked
involution and mover. All these images are returned for the same final
representative; the mover lies in S^c after the second conjugation.

The source identity C_T(Z) ≤ S remains an explicit premise. Its proof,
and movement of the changed short-root involution under the original S,
are still required for nonfusion. Original uniqueness, exhaustive compatible
comparison and ambient completion recognition remain separate obligations.
The Chapter12 companion applies both placements to the constructed marked
root pairs, without a supplied pair or placement witness.

Source: Aschbacher–Smith F.4.35, printed p.292, and the application in
5.3.3, p.659 (`refs/quasithin.pdf`). No new model computation is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem frattini_le_core_of_binary_quotient
    (K S : Subgroup G) (hSK : S ≤ K) (hS : IsPGroup 2 S)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (K ⧸ pCore 2 K) ≃* SL(2,F)) :
    (frattini S).map S.subtype ≤ K.pCoreIn 2 := by
  let f : S →* SL(2,F) := e.toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 K)).comp (inclusion hSK))
  obtain ⟨P,hP⟩ := (hS.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  let a := (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 P).symm
  have hs (x : S) : f x ^ 2 = 1 := by
    let y : P := ⟨f x,hP ⟨x,rfl⟩⟩
    have hy : y^2=1 := a.injective (by
      rw [map_pow,map_one,pow_two]
      change Multiplicative.ofAdd ((a y).toAdd + (a y).toAdd) = 1
      rw [CharTwo.add_self_eq_zero]
      rfl)
    exact congrArg Subtype.val hy
  rintro _ ⟨x,hx,rfl⟩
  have hh := frattini_le_ker_of_square_image f hs hx
  have hq : QuotientGroup.mk' (pCore 2 K) (inclusion hSK x) = 1 :=
    e.injective (hh.trans (map_one e).symm)
  exact mem_map_of_mem K.subtype ((QuotientGroup.eq_one_iff _).mp hq)

omit [Finite G] in
private theorem conjugate_centralizer (Z : Subgroup G) (g : G) :
    (centralizer (Z : Set G)).conjBy g = centralizer (Z.conjBy g : Set G) := by
  let e := MulAut.conj g
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
  intro z hz
  apply e.injective
  simpa only [map_mul,e.apply_symm_apply] using hx (e z) (mem_map_of_mem e.toMonoidHom hz)

omit [Finite G] in
private theorem conjBy_le_iff (U S : Subgroup G) (g : G) :
    U.conjBy g ≤ S ↔ U ≤ S.conjBy g⁻¹ := by
  constructor
  · intro hh u hu
    refine ⟨g*u*g⁻¹,hh (mem_map_of_mem _ hu),?_⟩
    change g⁻¹*(g*u*g⁻¹)*(g⁻¹)⁻¹=u
    group
  · intro hh
    rintro _ ⟨u,hu,rfl⟩
    obtain ⟨s,hs,he⟩ := hh hu
    change g⁻¹*s*(g⁻¹)⁻¹=u at he
    have hh : g*u*g⁻¹=s := by rw [←he]; group
    change g*u*g⁻¹ ∈ S
    rw [hh]
    exact hs

/-- The first Sylow conjugation keeps the conjugate root itself fixed. -/
theorem root_pair_first_placement
    (T : Sylow 2 G) (S Q Z U : Subgroup G)
    (hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G))
    (hCS : (T : Subgroup G) ⊓ centralizer (Z : Set G) ≤ S)
    (hSp : IsPGroup 2 S) (hUp : IsPGroup 2 U)
    (hPhiS : (frattini S).map S.subtype ≤ Q)
    (hPhiU : (frattini U).map U.subtype = Z)
    (g : G) (hUC : U ≤ centralizer (Z.conjBy g : Set G)) :
    ∃ g' : G, Z.conjBy g' = Z.conjBy g ∧ U ≤ S.conjBy g' ∧ Z ≤ Q.conjBy g' := by
  have hU0 : U.conjBy g⁻¹ ≤ centralizer (Z : Set G) := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hUC
    change U.conjBy g⁻¹ ≤ (centralizer (Z.conjBy g : Set G)).conjBy g⁻¹ at hh
    rw [conjugate_centralizer,←conjBy_mul,inv_mul_cancel,conjBy_one] at hh
    exact hh
  obtain ⟨c,hc,hcT⟩ := IsPGroup.exists_conj_le_sylow_of_normalized T
    (centralizer (Z : Set G)) (U.conjBy g⁻¹)
    (hTZ.trans (normalizer_le_normalizer_centralizer Z))
    (hUp.map _) hU0
  have hcZ : Z.conjBy c = Z :=
    mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _) hc)
  have hcC : (centralizer (Z : Set G)).conjBy c = centralizer (Z : Set G) := by
    rw [conjugate_centralizer,hcZ]
  have hcS : (U.conjBy g⁻¹).conjBy c ≤ S :=
    (le_inf hcT ((map_mono hU0).trans_eq hcC)).trans hCS
  have hUS : U ≤ S.conjBy (g*c⁻¹) := by
    rw [←conjBy_mul] at hcS
    simpa only [mul_inv_rev,inv_inv] using (conjBy_le_iff _ _ _).mp hcS
  refine ⟨g*c⁻¹,?_,hUS,?_⟩
  · rw [conjBy_mul]
    have hcZi : Z.conjBy c⁻¹ = Z :=
      mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _) ((centralizer (Z : Set G)).inv_mem hc))
    rw [hcZi]
  · rw [←hPhiU]
    have hh := frattini_image_le_of_le hUS (hSp.map (MulAut.conj (g*c⁻¹)).toMonoidHom)
    have hF : (frattini (S.conjBy (g*c⁻¹))).map (S.conjBy (g*c⁻¹)).subtype =
        ((frattini S).map S.subtype).conjBy (g*c⁻¹) :=
      frattini_image_map S (MulAut.conj (g*c⁻¹)).toMonoidHom (MulAut.conj (g*c⁻¹)).injective
    rw [hF] at hh
    exact hh.trans (map_mono hPhiS)

/-- Both placements use one final conjugator. The second conjugation fixes Z
pointwise but is recorded explicitly on every other subgroup. -/
theorem root_pair_two_placements
    (T : Sylow 2 G) (S Q Z U : Subgroup G)
    (hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G))
    (hCS : (T : Subgroup G) ⊓ centralizer (Z : Set G) ≤ S)
    (hSp : IsPGroup 2 S) (hQp : IsPGroup 2 Q)
    (hCQ : centralizer (Z : Set G) ≤ normalizer (Q : Set G))
    (hUQ : U ≤ Q)
    (hPhiS : (frattini S).map S.subtype ≤ Q)
    (hPhiU : (frattini U).map U.subtype = Z)
    (g : G) (hUC : U ≤ centralizer (Z.conjBy g : Set G)) :
    ∃ c g' : G, c ∈ centralizer (Z : Set G) ∧
      Z.conjBy g' = (Z.conjBy g).conjBy c ∧
      Z ≤ Q.conjBy g' ∧ Q.conjBy g' ⊓ centralizer (Z : Set G) ≤ S ∧
      U.conjBy c ≤ Q ∧ (frattini (U.conjBy c)).map (U.conjBy c).subtype = Z ∧
      U.conjBy c ≤ centralizer (Z.conjBy g' : Set G) := by
  obtain ⟨a,ha,hUa,hZa⟩ := root_pair_first_placement T S Q Z U hTZ hCS hSp
    (hQp.to_le hUQ) hPhiS hPhiU g hUC
  let R := Q.conjBy a ⊓ centralizer (Z : Set G)
  obtain ⟨c,hc,hcT⟩ := IsPGroup.exists_conj_le_sylow_of_normalized T
    (centralizer (Z : Set G)) R
    (hTZ.trans (normalizer_le_normalizer_centralizer Z))
    ((hQp.map (MulAut.conj a).toMonoidHom).to_le inf_le_left) inf_le_right
  have hcZ : Z.conjBy c = Z :=
    mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _) hc)
  have hcQ : Q.conjBy c = Q := mem_normalizer_iff_map_conj_eq.mp (hCQ hc)
  have hcC : (centralizer (Z : Set G)).conjBy c = centralizer (Z : Set G) := by
    rw [conjugate_centralizer,hcZ]
  have hR : R.conjBy c = Q.conjBy (c*a) ⊓ centralizer (Z : Set G) := by
    change (Q.conjBy a ⊓ centralizer (Z : Set G)).map (MulAut.conj c).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj c).injective]
    change (Q.conjBy a).conjBy c ⊓ (centralizer (Z : Set G)).conjBy c = _
    rw [←conjBy_mul,hcC]
  refine ⟨c,c*a,hc,?_,?_,?_,?_,?_,?_⟩
  · rw [conjBy_mul,ha]
  · have hh := map_mono (f := (MulAut.conj c).toMonoidHom) hZa
    change Z.conjBy c ≤ (Q.conjBy a).conjBy c at hh
    rwa [hcZ,←conjBy_mul] at hh
  · rw [←hR]
    exact (le_inf hcT ((map_mono (show R ≤ centralizer (Z : Set G) from inf_le_right)).trans_eq hcC)).trans hCS
  · exact (map_mono hUQ).trans_eq hcQ
  · have hF : (frattini (U.conjBy c)).map (U.conjBy c).subtype =
        ((frattini U).map U.subtype).conjBy c :=
      frattini_image_map U (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
    rw [hF,hPhiU,hcZ]
  · have hh := map_mono (f := (MulAut.conj c).toMonoidHom) hUC
    change U.conjBy c ≤ (centralizer (Z.conjBy g : Set G)).conjBy c at hh
    rwa [conjugate_centralizer,←ha,←conjBy_mul] at hh

private theorem frattini_le_core_of_psl
    (K S : Subgroup G) (hSK : S ≤ K) (hS : IsPGroup 2 S)
    {r : ℕ} (he : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^r)) :
    (frattini S).map S.subtype ≤ K.pCoreIn 2 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact frattini_le_core_of_binary_quotient K S hSK hS
    (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm)

/-- The original G₂ Sylow/core quotient has exponent two, so its Frattini
subgroup lies in the actual right two-core. -/
theorem Preparation.g2_source_frattini_le_core
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    (frattini (sourceS L H)).map (sourceS L H).subtype ≤ (residual H).pCoreIn 2 := by
  have hs := d.g2_local_structure h hTH hp F he
  exact frattini_le_core_of_psl _ _ (hs.2.2.2.2 1)
    (pCore_isPGroup.map _) hs.2.2.2.1

/-- The genuine triality arms quotient gives the same Frattini containment
for the original S, with its cubic-field quotient retained. -/
theorem Preparation.triality_source_frattini_le_core
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm)).reverse)) :
    (frattini (sourceS L H)).map (sourceS L H).subtype ≤ (residual H).pCoreIn 2 := by
  have hSK := d.triality_sourceS_le_factors h hTH hp m hm he 1
  rcases he with he | he
  · exact (d.not_triality_arms_left_amalgam h hTH hp
      (_root_.Triality.Standard.binaryParameters m hm) rfl he).elim
  obtain ⟨e⟩ := he
  exact frattini_le_core_of_psl _ _ hSK (pCore_isPGroup.map _)
    (d.triality_local_structure h hTH hp m hm e).2.2.2.2.1

/-- The two Sylow conjugations on the original right core. The source
centralizer identity remains explicit; neither required placement is assumed.
The second conjugator preserves Q and Z and is retained on the involution. -/
theorem source_special_core_placements
    {T : Sylow 2 G} {L H : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H)
    (hPhiS : (frattini (sourceS L H)).map (sourceS L H).subtype ≤ (residual H).pCoreIn 2)
    (hN : normalizer (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) =
      normalizer (residual H : Set G))
    (hCS : (T : Subgroup G) ⊓ centralizer
      (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤ sourceS L H)
    (U : Subgroup G) (hUQ : U ≤ (residual H).pCoreIn 2)
    (hPhiU : (frattini U).map U.subtype = (center (residual H)).map (residual H).subtype)
    (v : G) (hvQ : v ∈ (residual H).pCoreIn 2)
    (hvZ : v ∉ (center (residual H)).map (residual H).subtype)
    (g : G) (hvg : v ∈ ((center (residual H)).map (residual H).subtype).conjBy g)
    (hUC : U ≤ centralizer
      (((center (residual H)).map (residual H).subtype).conjBy g : Set G)) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ c g' : G, c ∈ centralizer (Z : Set G) ∧
      c*v*c⁻¹ ∈ Q ∧ c*v*c⁻¹ ∉ Z ∧ orderOf (c*v*c⁻¹) = orderOf v ∧
      c*v*c⁻¹ ∈ Z.conjBy g' ∧
      Z ≤ Q.conjBy g' ∧ Q.conjBy g' ⊓ centralizer (Z : Set G) ≤ sourceS L H ∧
      U.conjBy c ≤ Q ∧ (frattini (U.conjBy c)).map (U.conjBy c).subtype = Z ∧
      U.conjBy c ≤ centralizer (Z.conjBy g' : Set G) ∧
      ∀ x ∈ sourceS L H, ⁅x,v⁆ ∉ Z →
        c*x*c⁻¹ ∈ (sourceS L H).conjBy c ∧ ⁅c*x*c⁻¹,c*v*c⁻¹⁆ ∉ Z := by
  let K := residual H
  let Q := K.pCoreIn 2
  let Z := (center K).map K.subtype
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) := by
    rw [hN]
    exact hTH.trans (le_normalizer_residual H)
  have hCQ : centralizer (Z : Set G) ≤ normalizer (Q : Set G) :=
    ((Subgroup.centralizer_le_normalizer _).trans_eq hN).trans
      (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  obtain ⟨c,g',hc,hZg,hZQ,hRS,hUQc,hPhiUc,hUCc⟩ :=
    root_pair_two_placements T (sourceS L H) Q Z U hTZ hCS
      (pCore_isPGroup.map _) (isPGroup_pCoreIn 2 K) hCQ hUQ hPhiS hPhiU g hUC
  have hcZ : c ∈ normalizer (Z : Set G) := (Subgroup.centralizer_le_normalizer _) hc
  have hcg : c*v*c⁻¹ ∈ Z.conjBy g' := by
    rw [hZg]
    exact mem_map_of_mem _ hvg
  refine ⟨c,g',hc,(mem_normalizer_iff.mp (hCQ hc) v).mp hvQ,
    fun he => hvZ ((mem_normalizer_iff.mp hcZ v).mpr he),
    (MulAut.conj c).orderOf_eq v,hcg,hZQ,hRS,hUQc,hPhiUc,hUCc,?_⟩
  intro x hx hxv
  refine ⟨mem_map_of_mem _ hx,?_⟩
  intro hh
  have he : ⁅c*x*c⁻¹,c*v*c⁻¹⁆ = c*⁅x,v⁆*c⁻¹ :=
    (map_commutatorElement (MulAut.conj c).toMonoidHom x v).symm
  rw [he] at hh
  exact hxv ((mem_normalizer_iff.mp hcZ _).mpr hh)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
