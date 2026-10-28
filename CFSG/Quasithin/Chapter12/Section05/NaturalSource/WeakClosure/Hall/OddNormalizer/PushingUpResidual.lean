module
public import CFSG.Quasithin.Chapter4.Section02.MathieuResidual
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpMathieu
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore

/-!
# The full cubic residual in the exterior pushing-up branch

The previously constructed M₂₂ component is now identified with the entire
solvable residual of C_K(x). The full J₄ cover has two-group center and a
single factor five. The rank and order argument in MathieuResidual excludes
all other C-components, and the source component-generation theorem gives
the residual equality. Characteristicity gives normality in C_H(x).

The original exterior cubic, sixteen fixed vectors, full module of order
at least 1024, actual PSL₅(2) section and all literal embeddings are retained.
The residual has the genuine M₂₂ triple cover as its two-core quotient and
escapes the marked normalizer. Quasisimplicity of the full residual, promotion
to C_G(x) and the final commutator contradiction remain to be proved. The
separate p.623 odd-local comparison is unchanged.
Source: Aschbacher--Smith, 4.2.13, printed p.612; the literal Hall application
is in OddNormalizer, using 12.2.11(a), pp.798--799.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 Chapter12.Section02
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter7.NormalizedSource.MathieuGeneration
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]


private def normalCentralizerEquiv {H : Type*} [Group H]
    (K : Subgroup H) (k : K) :
    centralizer ({k} : Set K) ≃* K.subgroupOf (centralizer ({(k : H)} : Set H)) where
  toFun c := ⟨⟨c.val.val,mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp c.property))⟩,c.val.property⟩
  invFun c := ⟨⟨c.val.val,c.property⟩,mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp c.val.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The cubic residual is normal in the centralizer in the whole local
witness H. This is relative normality, prior to passage to C_G(x). -/
theorem exterior_pushingUp_cubic_residual_normal {H : Type*} [Group H] [Finite H]
    (K : Subgroup H) [K.Normal] (k : K) :
    ((solvableResidual (centralizer ({k} : Set K))).map
      (K.subtype.elementCentralizerMap k)).Normal := by
  let C := centralizer ({(k : H)} : Set H)
  let B := K.subgroupOf C
  let e := normalCentralizerEquiv K k
  have he : (solvableResidual (centralizer ({k} : Set K))).map
      (K.subtype.elementCentralizerMap k) = (solvableResidual B).map B.subtype := by
    rw [←map_solvableResidual_eq e.toMonoidHom e.surjective,map_map]
    rfl
  rw [he]
  let : B.Normal := inferInstanceAs (K.subgroupOf C).Normal
  apply normalizer_eq_top_iff.mp
  exact top_unique (show (⊤ : Subgroup C) ≤ _ from by
    rw [←(show normalizer (B : Set C) = ⊤ from normalizer_eq_top B)]
    exact normalizer_le_normalizer_characteristic_image B (solvableResidual B))

private theorem pushingUp_cover_not_twentyFive
    {L V A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K) (e : (K ⧸ center K) ≃* Janko4.Model) :
    ¬ 25 ∣ Nat.card K := by
  let := hK.2
  have ho : pPrimeCore 2 K = ⊥ := hK.1.pPrimeCore_eq_bot
    hw.2.2.2.2.2.2.2.2.2.2.2.2.1 K
  have hz : IsPGroup 2 (center K) := by
    rw [IsQuasisimple.center_eq_pCore ho]
    exact pCore_isPGroup
  obtain ⟨n,hn⟩ := hz.exists_card_eq
  intro hd
  rw [card_eq_card_quotient_mul_card_subgroup (center K),Nat.card_congr e.toEquiv,
    Janko4.Cardinality.model_card,hn] at hd
  have hc : Nat.Coprime 25 (2 ^ n) := (by decide : Nat.Coprime 25 2).pow_right n
  exact (by decide : ¬25 ∣ 86775571046077562880) (hc.dvd_of_dvd_mul_right hd)

variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The full residual at the prescribed cubic has the actual triple Mathieu
two-core quotient and escapes the marked exterior normalizer. -/
theorem exterior_pushingUp_full_cubic_residual (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K) (hn : K.Normal)
    (e : (K ⧸ center K) ≃* Janko4.Model) (k : K) (hk : orderOf k = 3) :
    let R := solvableResidual (centralizer ({k} : Set K))
    R.IsCComponent ∧ IsM22Cover (R ⧸ pCore 2 R) ∧
      (R.map (K.subtype.elementCentralizerMap k)).Normal ∧
      (⟨k,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({k} : Set K)) ∈ R ∧
      Nonempty ((R ⧸ solvableRadical R) ≃* Sporadic.Mathieu.M22) ∧
      ¬ R.map (H.subtype.comp (K.subtype.comp
        (centralizer ({k} : Set K)).subtype)) ≤ s.marking.M := by
  obtain ⟨Q,hQ,hnQ,hm,hkQ,⟨eq⟩,hout⟩ :=
    exterior_pushingUp_cubic_component_escape s h hw K hn e k hk
  have hC : IsSQTK KnownSimple.IsKnownSimple (centralizer ({k} : Set K)) :=
    (hw.2.2.2.2.2.2.1.sqtk.subgroup K).subgroup _
  have h25 : ¬25 ∣ Nat.card (centralizer ({k} : Set K)) := fun hd =>
    pushingUp_cover_not_twentyFive hw K hK e (hd.trans (card_subgroup_dvd_card _))
  let := hn
  have hnormal := exterior_pushingUp_cubic_residual_normal K k
  dsimp only
  rw [Chapter4.Section02.mathieu_component_eq_solvableResidual hC h25 hQ eq] at hnormal ⊢
  exact ⟨hQ,hm,hnormal,hkQ,⟨eq⟩,hout⟩

/-- The original exterior pushing-up case with the whole cubic residual.
The residual is normal in C_H(x); no ambient normality is assumed. -/
@[expose] def ExteriorPushingUpFullResidualCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ s.marking.M.subgroupOf H ∧
    1024 ≤ Nat.card W ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    Nonempty ((F ⧸ pCore 2 F) ≃* Representation.SL5TenDimensional.Group) ∧
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ s.marking.M).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      V ≤ K.map H.subtype ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ (x : F) (k : K), ((k : H) : G) = (x : G) ∧ orderOf x = 3 ∧ orderOf k = 3 ∧
        16 ≤ Nat.card (V ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) ∧
        let R := solvableResidual (centralizer ({k} : Set K))
        R.IsCComponent ∧ IsM22Cover (R ⧸ pCore 2 R) ∧
          (R.map (K.subtype.elementCentralizerMap k)).Normal ∧
          (⟨k,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({k} : Set K)) ∈ R ∧
          Nonempty ((R ⧸ solvableRadical R) ≃* Sporadic.Mathieu.M22) ∧
          ¬ R.map (H.subtype.comp (K.subtype.comp
            (centralizer ({k} : Set K)).subtype)) ≤ s.marking.M

/-- Identify the entire cubic residual on the original exterior witnesses. -/
theorem exterior_pushingUp_full_residual_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A : Subgroup G} (hj : ExteriorPushingUpCubicComponentCase s A) :
    ExteriorPushingUpFullResidualCase s A := by
  obtain ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,_⟩ := hj
  exact ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    x,k,hkx,hx,hk,hfix,exterior_pushingUp_full_cubic_residual s h hw K hK hn e k hk⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
