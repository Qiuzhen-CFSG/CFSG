module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearWeylEscape
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstPrimeLinear

/-!
# Escape from the original maximal local subgroup in the linear triangle

The Weyl calculation supplies a normalizer outside a marked parabolic. To
obtain the source conclusion outside M = N_G(L), first prove that every
proper Sylow overgroup of a local component in Sp₄(4) or G₂(4) normalizes
that component. Parabolic placement, perfectness and the rank-one cover
calculation identify the component with the containing parabolic residual.

Apply this to the image of I ∩ M under the original two-core quotient.
The image remains proper: its preimage already contains the kernel,
because M contains T. Coprime normalizer lifting now gives an element of
I ∩ N_G(X₂) outside M. The original identity X₁ = X₂ supplies the same
conclusion for X₁. Strictness of the original containing component proves
I is not contained in M; this is discharged in the literal consumer.

Thus the source conclusion N_G(X₁) ≰ M is established without needing
the stronger intermediate equality I ∩ M = L₂X. Common-normal existence,
the centralizer/module argument excluding the original SL₃(4), both
orientations and full 11.1.1--3 remain with
qt-d-1222-natural-relative-components. Earlier-source inputs retain their
producers and final discharge by qt-d-1222-natural-local-geometry.
Source: Aschbacher--Smith 11.1.2, printed p.763. The G₂ model uses the
existing licensed ATLAS port (LICENSES/ATLAS.txt).
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.Section03 CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section

private theorem local_perfect {A : Type*} [Group A] {B P : Subgroup A}
    (hB : B ∈ localCComponents P) : Group.IsPerfect B := by
  let := hB.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ P from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective

private theorem normalizes_of_conjugate {A : Type*} [Group A]
    (H B : Subgroup A) (a : MulAut A)
    (h : H.map a.toMonoidHom ≤ normalizer (B.map a.toMonoidHom : Set A)) :
    H ≤ normalizer (B : Set A) := by
  rw [←map_equiv_normalizer_eq] at h
  exact (map_le_map_iff_of_injective a.injective).mp h

namespace Sp4Weyl
open Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem sylow_le_local (W : Submodule F (Vector F))
    (S : Sylow 2 (Sp F)) (hS : (S : Subgroup (Sp F)) ≤ stabilizer W) :
    (S : Subgroup (Sp F)) ≤ determinantKernel W := by
  intro t ht
  let x : stabilizer W := ⟨t,hS ht⟩
  obtain ⟨n,hn⟩ := S.isPGroup'.exists_pow_pow_eq_one ⟨t,ht⟩
  have hx : x^(2^n)=1 := Subtype.ext (congrArg (fun y : S => (y : Sp F)) hn)
  have hp := congrArg (fun u : Fˣ => (u : F)) (congrArg (determinantCharacter W) hx)
  refine ⟨x,?_,rfl⟩
  apply Units.ext
  exact (iterateFrobenius_inj F 2 n) (by simpa [iterateFrobenius_def] using hp)

/-- A proper Sylow overgroup normalizes every local component it contains. -/
theorem proper_overgroup_normalizes (hF : Nat.card F = 4)
    (S : Sylow 2 (Sp F)) (B H : Subgroup (Sp F))
    (hB : B ∈ localCComponents S) (hBH : B ≤ H)
    (hSH : (S : Subgroup (Sp F)) ≤ H) (hH : H ≠ ⊤) :
    H ≤ normalizer (B : Set (Sp F)) := by
  obtain ⟨g,hg⟩ := ThreeResidualPlacement.proper_sylow_overgroup_parabolic_cover
    (by omega) S H hSH hH
  let a := MulAut.conj g
  let S' := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker hB a.toMonoidHom
  let := local_perfect hl
  apply normalizes_of_conjugate H B a
  rcases hg with hp | hp
  · let := pointLocal_perfect (n := 2) hF (by decide)
    have hb : B.map a.toMonoidHom ≤ pointLocal := by
      rw [←pointParabolic_solvableResidual_eq (n := 2) hF (by decide)]
      exact le_map_solvableResidual_of_isPerfect _ _ ((map_mono hBH).trans hp)
    have he := FiveLocalFF.local_eq_of_sl2_core_quotient pointLocal (by omega)
      (pointLocalCoreQuotientEquiv (n := 2) hF (by decide)) S' _ hl hb
      (sylow_le_local (point F) S' ((map_mono hSH).trans hp))
    rw [he]
    exact hp.trans (le_normalizer_of_normal_subgroupOf pointLocal_le)
  · let := planeLocal_perfect (n := 2) hF (by decide)
    have hb : B.map a.toMonoidHom ≤ planeLocal := by
      rw [←planeParabolic_solvableResidual_eq (n := 2) hF (by decide)]
      exact le_map_solvableResidual_of_isPerfect _ _ ((map_mono hBH).trans hp)
    have he := FiveLocalFF.local_eq_of_sl2_core_quotient planeLocal (by omega)
      (planeLocalCoreQuotientEquiv (n := 2) hF (by decide)) S' _ hl hb
      (sylow_le_local (plane F) S' ((map_mono hSH).trans hp))
    rw [he]
    exact hp.trans (le_normalizer_of_normal_subgroupOf planeLocal_le)
end Sp4Weyl

namespace G2Weyl
open Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped Pointwise
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The same proper-overgroup control holds in the literal G₂ model. -/
theorem proper_overgroup_normalizes (hF : Nat.card F = 4)
    (S : Sylow 2 (Model F)) (B H : Subgroup (Model F))
    (hB : B ∈ localCComponents S) (hBH : B ≤ H)
    (hSH : (S : Subgroup (Model F)) ≤ H) (hH : H ≠ ⊤) :
    H ≤ normalizer (B : Set (Model F)) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model F) S (sylow (F := F))
  have hSU : (S : Subgroup (Model F)).map (MulAut.conj g).toMonoidHom = unipotent := by
    rw [←sylow_coe,←hg,Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def]
    rfl
  let a := MulAut.conj g
  let S' := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker hB a.toMonoidHom
  let := local_perfect hl
  have hp := ProperSylowOvergroups.le_parabolic (H.map a.toMonoidHom)
    (hSU ▸ map_mono hSH) (lt_top_iff_ne_top.mpr (by
      intro ht
      apply hH
      apply map_injective (f := a.toMonoidHom) a.injective
      rw [ht,map_top_of_surjective _ a.surjective]))
  apply normalizes_of_conjugate H B a
  rcases hp with hp | hp
  · let := local₁_isPerfect (by omega : 2 < Nat.card F)
    have hb : B.map a.toMonoidHom ≤ local₁ := by
      rw [←HigherFieldResiduals.parabolic₁_residual (by omega : 2 < Nat.card F)]
      exact le_map_solvableResidual_of_isPerfect _ _ ((map_mono hBH).trans hp)
    have he := FiveLocalFF.local_eq_of_sl2_core_quotient local₁ (by omega)
      (local₁CoreQuotientEquivPSL.trans longSLEquivPSL.symm) S' _ hl hb
      (by change (S : Subgroup (Model F)).map a.toMonoidHom ≤ local₁
          rw [hSU]; exact unipotent_le_local₁)
    rw [he]
    exact hp.trans parabolic₁_normalizes_local₁
  · let := local₂_isPerfect (by omega : 2 < Nat.card F)
    have hb : B.map a.toMonoidHom ≤ local₂ := by
      rw [←HigherFieldResiduals.parabolic₂_residual (by omega : 2 < Nat.card F)]
      exact le_map_solvableResidual_of_isPerfect _ _ ((map_mono hBH).trans hp)
    have he := FiveLocalFF.local_eq_of_sl2_core_quotient local₂ (by omega)
      (local₂CoreQuotientEquivPSL.trans longSLEquivPSL.symm) S' _ hl hb
      (by change (S : Subgroup (Model F)).map a.toMonoidHom ≤ local₂
          rw [hSU]; exact unipotent_le_local₂)
    rw [he]
    exact hp.trans parabolic₂_le_normalizer_local₂
end G2Weyl

private theorem escape_from_sylow_overgroup_through_two_kernel
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    (T : Sylow 2 G) {B I M E : Subgroup G}
    (hB : B ∈ localCComponents T) (hI : I ∈ localCComponents T)
    (hBI : B < I) (hBM : B ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hIM : ¬ I ≤ M) (hEI : E ≤ I) (hEM : E ≤ M) (hE : IsPGroup 3 E)
    (q : I →* A) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (control : ∀ (P : Sylow 2 A) (C H : Subgroup A),
      C ∈ localCComponents P → C ≤ H → (P : Subgroup A) ≤ H → H ≠ ⊤ →
      H ≤ normalizer (C : Set A))
    (escape : ∀ (P : Sylow 2 A) (C U : Subgroup A),
      C ∈ localCComponents P → C ≠ ⊤ → IsPGroup 3 U →
      U ≤ normalizer (C : Set A) → ¬ normalizer (U : Set A) ≤ normalizer (C : Set A)) :
    ¬ I ⊓ normalizer (E : Set G) ≤ M := by
  obtain ⟨P,hP,hBP⟩ := BinaryIntrinsic.local_in_local_overgroup T hB hI hBI.le
  let : Group.IsNilpotent q.ker := hk.isNilpotent
  let : Group.IsSolvable q.ker := inferInstance
  have hPM : (P : Subgroup I) ≤ M.subgroupOf I := by
    rw [hP]
    exact comap_mono hTM
  have hproper : (M.subgroupOf I).map q ≠ ⊤ := by
    intro he
    have hh := congrArg (comap q) he
    rw [comap_map_eq_self ((hk.le_sylow_of_normal P).trans hPM),comap_top] at hh
    exact hIM (subgroupOf_eq_top.mp hh)
  have hb := Chapter1.Section02.localCComponents_map_of_solvable_ker hBP q
  have hbp : (B.subgroupOf I).map q ≠ ⊤ :=
    fun he => hproper (top_unique (he ▸ map_mono (comap_mono hBM)))
  have hc := control (P.mapSurjective hq) ((B.subgroupOf I).map q)
    ((M.subgroupOf I).map q) hb (map_mono (comap_mono hBM)) (map_mono hPM) hproper
  have hn := escape (P.mapSurjective hq) ((B.subgroupOf I).map q)
    ((E.subgroupOf I).map q) hb hbp (hE.comap_subtype.map q)
    ((map_mono (comap_mono hEM)).trans hc)
  have hout := normalizer_not_le_of_two_kernel q hq hk (M.subgroupOf I) (E.subgroupOf I)
    (p := 3) (by decide) hE.comap_subtype (fun he => hn (he.trans hc))
  intro he
  apply hout
  rw [←subgroupOf_normalizer_eq hEI]
  intro x hx
  exact he ⟨x.property,hx⟩

/-- In either recognized field-four model, a cubic in a proper Sylow
overgroup has an original normalizer escaping that overgroup. -/
theorem local_four_cubic_normalizer_escapes_overgroup
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) {B I M E : Subgroup G}
    (hB : B ∈ localCComponents T) (hI : I ∈ localCComponents T)
    (hBI : B < I) (hBM : B ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hIM : ¬ I ≤ M) (hEI : E ≤ I) (hEM : E ≤ M) (hE : IsPGroup 3 E)
    (hm : Source.IsSp (I ⧸ pCore 2 I) 2 4 ∨ ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4) :
    ¬ I ⊓ normalizer (E : Set G) ≤ M := by
  rcases hm with hm | hm
  all_goals
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
      (show Nat.card F = 2^2 by simpa using hF)
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
    have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : IsPGroup 2 q.ker := by
      rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,QuotientGroup.ker_mk']
      exact pCore_isPGroup
    apply escape_from_sylow_overgroup_through_two_kernel T hB hI hBI hBM hTM
      hIM hEI hEM hE q hq hk
  · exact Sp4Weyl.proper_overgroup_normalizes hF
  · exact Sp4Weyl.local_escape hF
  · exact G2Weyl.proper_overgroup_normalizes hF
  · exact G2Weyl.local_escape hF

open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource Representation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- The original linear common-Q triangle forces both equal Cartan cubic
normalizers outside M = N_G(L), as required before the source centralizer
and module comparison. No intersection identity or extra placement is assumed. -/
theorem linear_triangle_cubic_normalizers_not_le_original_maximal_of_common_normal
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hgen : f.Li 0 ⊔ K₀ = K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    (¬ normalizer ((X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) ∧
    (¬ normalizer ((X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) := by
  let I := K₀ ⊔ f.Li 1
  obtain ⟨_,hIL,_,hXI,_,_,_,hmodels⟩ := linear_triangle_join_two_models_of_common_normal
    D S m f hd hfix hX hK hLK hK₀ hK₀K hTK₀ hgen hk hp hcard hmove hQ hQT hTQ hKQ hLQ
  obtain ⟨_,hc,_,_⟩ := linear_triangle_proper_residuals D S m f hd hX hK hLK hK₀ hK₀K hk hp
  have hm (i : Fin 2) : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2^S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,
      ⟨SL3.flagLocalCoreEquiv S m f i⟩⟩
  have hli (i : Fin 2) : f.Li i ≤ L := (localResidual_le _).trans inf_le_left
  have hIM : ¬ I ≤ normalizer (L : Set G) := by
    intro he
    have hKM : K ≤ normalizer (L : Set G) := by
      rw [←hgen]
      exact sup_le ((hli 0).trans L.le_normalizer) (le_sup_left.trans he)
    exact hLK.ne (flag_component_eq_of_le_component_normalizer D S f 0
      (hm 0) hK.1 hLK.le hKM)
  have hout := local_four_cubic_normalizer_escapes_overgroup T
    (flag_mem_local_of_model D S f 1 (hm 1)).1 hIL.1 hc
    ((hli 1).trans L.le_normalizer) D.sylow_normalizes_component hIM
    (inf_le_left.trans hXI)
    (inf_le_left.trans ((hX.1.trans inf_le_left).trans L.le_normalizer))
    (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hcard)) hmodels
  have hn : ¬ normalizer ((X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) : Set G) ≤
      normalizer (L : Set G) := fun he => hout (inf_le_right.trans he)
  refine ⟨?_,hn⟩
  simpa only [linear_four_cartan_kernels_eq D S m hd f hX] using hn

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
