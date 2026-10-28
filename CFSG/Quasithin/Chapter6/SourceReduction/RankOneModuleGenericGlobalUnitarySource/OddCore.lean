module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MaximalNormalizer
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.MaximalNormalizerOddCore
public import Theory.GroupTheory.CharacteristicTwoInheritance
public import Theory.GroupTheory.SelfCentralizingCore
-- Internal map reduction for the literal residual-to-ambient centralizer embedding.
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortQuotient

/-!
# Odd-core exclusion in the prepared unitary maximal-W normalizer

The original right-core center has order q>2. Odd outer degree places it
in L, and ambient long-root return places it in O₂(L). The elementary
left core centralizes the short root and every W in the fixed line, so the
local W-normalizer contains that entire core and has characteristic two.
Generation by the long-root involution centralizers absorbs the odd core
of the full W-normalizer into this local subgroup, where it is trivial.

Apply central-kernel descent and full I.8.5 to this same maximal W. Its
quotient normal closure is centerless and satisfies the marked Bender/Borel
alternative; the cyclic alternative is excluded. The whole kernel W,
both input orientations, degree-two rows and q=4 remain present.

Source: Aschbacher–Smith F.4.42, printed p.296. The perfect-actor
contradiction, outer transfer and ambient order comparison remain required.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The marked common-centralizer bound kills the odd core of every
normalizer of a subgroup of the original elementary left core. The source
application below supplies this bound for its same short root. -/
theorem Preparation.unitary_short_normalizer_odd_core_of_odd_outer
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm)
    (hodd : ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier)
    (t : L) (htQ : t.val ∈ L.pCoreIn 2)
    (hcommon : ∀ z ∈ (center (residual H)).map (residual H).subtype, orderOf z = 2 →
      centralizer ({t.val} : Set G) ⊓ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (W₀ : Subgroup (centralizer ({t.val} : Set G)))
    (hWQ : W₀.map (centralizer ({t.val} : Set G)).subtype ≤ L.pCoreIn 2) :
    pPrimeCore 2 (normalizer (W₀ : Set (centralizer ({t.val} : Set G)))) = ⊥ := by
  let M := centralizer ({t.val} : Set G)
  let N := normalizer (W₀ : Set M)
  let X := (normalizer (L : Set G)).subgroupOf M
  let D := X.subgroupOf N
  let j : N →* G := M.subtype.comp N.subtype
  have hj : Function.Injective j := M.subtype_injective.comp N.subtype_injective
  obtain ⟨hmgt,_,hQelem,_,_,hZcard,_,_,hZelem,hZK⟩ :=
    d.unitary_core_structure h hH.1.1.2 hp m hm hc
  let : IsElementaryAbelian 2 (pCore 2 L) := hQelem
  let : IsElementaryAbelian 2 (L.pCoreIn 2) := IsElementaryAbelian.map L.subtype
  let Z := center (pCore 2 (residual H))
  let : IsElementaryAbelian 2 Z := hZelem
  let k : Z →* G := (residual H).subtype.comp ((pCore 2 (residual H)).subtype.comp Z.subtype)
  have hk : Function.Injective k := (residual H).subtype_injective.comp
    ((pCore 2 (residual H)).subtype_injective.comp Z.subtype_injective)
  have hkZ (z : Z) : k z ∈ (center (residual H)).map (residual H).subtype :=
    mem_map_of_mem (residual H).subtype (hZK (mem_map_of_mem _ z.property))
  have hKT : (residual H).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hKN := le_normalizer_residual H
    obtain ⟨S,hS⟩ := exists_sylow_component (hH.1.1.2.trans hKN)
    exact ((map_mono (pCore_isPGroup.le_sylow_of_normal S)).trans_eq hS).trans inf_le_left
  have hTL : (T : Subgroup G) ≤ L :=
    (d.unitaryFour_two_subgroups_of_odd_outer h hH hp m hm hc r hodd).1
      (T : Subgroup G) T.isPGroup' h.sylow_normalizes
  have hkQ (z : Z) : k z ∈ L.pCoreIn 2 := by
    by_cases hz : k z = 1
    · rw [hz]; exact one_mem _
    have hzL : k z ∈ L := hTL (hKT (mem_map_of_mem _ z.val.property))
    exact mem_map_of_mem L.subtype (d.unitary_long_residual_return h hH hp m hm hc
      (k z) (hkZ z) (d.unitary_right_center_involutions h hH hp m hm hc _ (hkZ z) hz)
      ⟨k z,hzL⟩ (IsConj.refl _))
  have commQ {a b : G} (ha : a ∈ L.pCoreIn 2) (hb : b ∈ L.pCoreIn 2) : a*b=b*a :=
    congrArg Subtype.val (mul_comm (⟨a,ha⟩ : L.pCoreIn 2) ⟨b,hb⟩)
  have hQN (a : G) (ha : a ∈ L.pCoreIn 2) :
      ∃ b : N, j b = a := by
    let aM : M := ⟨a,mem_centralizer_singleton_iff.mpr (commQ ha htQ)⟩
    have haN : aM ∈ N := by
      apply Subgroup.centralizer_le_normalizer
      intro w hw
      exact Subtype.ext (commQ (hWQ (mem_map_of_mem M.subtype hw)) ha)
    exact ⟨⟨aM,haN⟩,rfl⟩
  have hQD : L.pCoreIn 2 ≤ D.map j := by
    intro a ha
    obtain ⟨b,hb⟩ := hQN a ha
    refine ⟨b,?_,hb⟩
    change j b ∈ normalizer (L : Set G)
    rw [hb]
    exact L.le_normalizer (pCoreIn_le 2 L ha)
  have hDN : D.map j ≤ normalizer (L : Set G) := by
    rintro a ⟨b,hb,rfl⟩
    exact hb
  have hloc := d.unitary_normalizer_local_conditions h hH hp m hm hc
  have hNL : normalizer (L : Set G) ⊓
      centralizer ((normalizer (L : Set G)).pCoreIn 2 : Set G) ≤
        (normalizer (L : Set G)).pCoreIn 2 :=
    (inf_centralizer_pCoreIn_le_iff 2 _).mpr
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hloc.fitting_left)
  have hcore : (normalizer (L : Set G)).pCoreIn 2 = L.pCoreIn 2 := hloc.twoCore_left
  have hchar := pCoreIn_selfCentralizing_of_core_centralizer_le hNL hDN
    (inf_le_left.trans (hcore.symm ▸ hQD))
  have hcD : centralizer (pCore 2 D : Set D) ≤ pCore 2 D := by
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (D.equivMapOfInjective j hj)).mpr
      ((inf_centralizer_pCoreIn_le_iff 2 (D.map j)).mp hchar)
  have hOD : pPrimeCore 2 D = ⊥ := pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hcD
  let f : Z →* N :=
    { toFun := fun z => Classical.choose (hQN (k z) (hkQ z))
      map_one' := hj (by simpa only [map_one] using Classical.choose_spec (hQN (k 1) (hkQ 1)))
      map_mul' := fun a b => hj (by
        exact (Classical.choose_spec (hQN (k (a*b)) (hkQ (a*b)))).trans
          ((k.map_mul a b).trans ((congrArg₂ (· * ·)
            (Classical.choose_spec (hQN (k a) (hkQ a))).symm
            (Classical.choose_spec (hQN (k b) (hkQ b))).symm).trans (j.map_mul _ _).symm))) }
  have hf (z : Z) : j (f z) = k z := Classical.choose_spec (hQN (k z) (hkQ z))
  have hfi : Function.Injective f := fun a b he => hk ((hf a).symm.trans ((congrArg j he).trans (hf b)))
  let E := f.range
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hE : 2 < Nat.card E := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv,hZcard]
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) hmgt
  apply oddCore_eq_bot_of_elementary_centralizers E D hE hOD
  rintro _ ⟨z,rfl⟩ hz a ha
  have hz1 : k z ≠ 1 := by
    intro he
    apply hz
    apply hj
    rw [hf,map_one,he]
  have hcomm : j a ∈ centralizer ({k z} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg j (mem_centralizer_singleton_iff.mp ha)
    simpa only [map_mul,hf] using he
  exact hcommon (k z) (hkZ z)
    (d.unitary_right_center_involutions h hH hp m hm hc _ (hkZ z) hz1)
    ⟨a.val.property,hcomm⟩

/-- On the same prepared maximal-W section, both the ambient normalizer
odd core and the quotient normal-closure center are trivial. All Bender,
Borel, Sylow and automizer clauses of I.8.5 are retained. -/
theorem Preparation.unitary_short_maximal_bender_of_odd_outer
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm)
    (hodd : ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
      z.val.val ∈ (center (residual H)).map (residual H).subtype ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ _hU : U ≤ center (centralizer ({t} : Set L)),
      Nat.card U = 2^m ∧ IsElementaryAbelian 2 U ∧
      let M := centralizer ({t.val} : Set G)
      let X := (normalizer (L : Set G)).subgroupOf M
      let U₀ := U.map (UnitarySource.shortCentralizerEmbedding L t)
      let t₀ := UnitarySource.shortCentralizerEmbedding L t
        ⟨t,mem_centralizer_singleton_iff.mpr rfl⟩
      normalizer (U₀ : Set M) = X ∧ (X ≠ ⊤ →
    ∃ W : Subgroup M, zpowers t₀ ≤ W ∧ W < U₀ ∧ ¬ normalizer (W : Set M) ≤ X ∧
      (∀ R : Subgroup M, W < R → R ≤ U₀ → normalizer (R : Set M) ≤ X) ∧
      let N := normalizer (W : Set M)
      pPrimeCore 2 N = ⊥ ∧
      let f := QuotientGroup.mk' (W.subgroupOf N)
      let V := (U₀.subgroupOf N).map f
      let Y := (X.subgroupOf N).map f
      V ≠ ⊥ ∧ Y ≠ ⊤ ∧ normalizer (V : Set (N ⧸ W.subgroupOf N)) = Y ∧
      IsElementaryAbelian 2 V ∧
      ∃ hnormal : (V.subgroupOf Y).Normal, letI := hnormal;
      (∀ v ∈ V, v ≠ 1 → ∃! q : (N ⧸ W.subgroupOf N) ⧸ Y, v • q = q) ∧
      (let K := normalClosure (V : Set (N ⧸ W.subgroupOf N))
       pPrimeCore 2 K = ⊥ ∧ center K = ⊥ ∧ IsQuasisimple K ∧ BenderSuzuki.IsSimpleBenderGroup (K ⧸ center K) ∧
           Y.comap K.subtype = normalizer (V.subgroupOf K : Set K) ∧
           BenderSuzuki.IsBorelSubgroup (Y.comap K.subtype) ∧
           ∃ S : Sylow 2 K, (S : Subgroup K) ≤ Y.comap K.subtype ∧
             V.subgroupOf K = (omega₁ S (p := 2)).map (S : Subgroup K).subtype) ∧
      Group.IsSolvable (Y ⧸ centralizer (V.subgroupOf Y : Set Y))) := by
  obtain ⟨hmgt,hn,t,ht,htQ,hcommon,z,hz,hzc,U,hU,hUQ,hUV,hUc,_,_,_,htU,
      hfix,_,_,hNU,hV,P,hPX,hzP,hPcentral⟩ :=
    d.unitary_short_fixed_cosets_sylow_with_core_of_odd_outer h hH hp m hm hc r hodd
  let M := centralizer ({t.val} : Set G)
  let X := (normalizer (L : Set G)).subgroupOf M
  let j := UnitarySource.shortCentralizerEmbedding L t
  let U₀ := U.map j
  let t₀ := j ⟨t,mem_centralizer_singleton_iff.mpr rfl⟩
  let : IsElementaryAbelian 2 (normalClosure ({z} : Set (centralizer ({t} : Set L)))) := hV
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (inclusion hUV) (inclusion_injective _)
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.map j
  have hUX : U₀ ≤ X := by
    rintro a ⟨b,_,rfl⟩
    exact L.le_normalizer b.val.property
  have htU₀ : t₀ ∈ U₀ := mem_map_of_mem j (htU.le (mem_zpowers _))
  have htcenter : t₀ ∈ center M := by
    apply mem_center_iff.mpr
    intro b
    exact Subtype.ext (mem_centralizer_singleton_iff.mp b.property)
  refine ⟨hmgt,hn,t,ht,z,hz,hzc,U,hU,hUc,inferInstance,hNU,?_⟩
  intro hX
  obtain ⟨W₀,hZW,hWU,hWX,hmax,hsection⟩ :=
    ChapterF.UnitarySource.maximal_normalizer_section X U₀ (zpowers t₀)
      hX hUX (zpowers_le.mpr htU₀) (zpowers_le.mpr htcenter) hNU
      P hPX (j z) hzP hPcentral hfix
  have hU₀Q : U₀.map M.subtype ≤ L.pCoreIn 2 := by
    change (U.map j).map M.subtype ≤ L.pCoreIn 2
    rw [map_map]
    change U.map (L.subtype.comp (centralizer ({t} : Set L)).subtype) ≤ L.pCoreIn 2
    simpa only [map_map] using hUQ
  have hON := d.unitary_short_normalizer_odd_core_of_odd_outer h hH hp m hm hc r hodd t htQ hcommon W₀
    ((map_mono hWU.le).trans hU₀Q)
  obtain ⟨hVne,hYne,hNY,hVe,hVN,hfixV,_,hsol⟩ := hsection
  let N := normalizer (W₀ : Set M)
  have hUN : U₀ ≤ N := by
    intro u hu
    apply Subgroup.centralizer_le_normalizer
    intro w hw
    exact congrArg Subtype.val (mul_comm (⟨w,hWU.le hw⟩ : U₀) ⟨u,hu⟩)
  let : IsElementaryAbelian 2 (U₀.subgroupOf N) := IsElementaryAbelian.subgroupOf hUN
  have hb := ChapterF.UnitarySource.quotient_bender_of_odd_core
    (U₀.subgroupOf N) (W₀.subgroupOf N) (comap_mono hWU.le) hON
    ((X.subgroupOf N).map (QuotientGroup.mk' (W₀.subgroupOf N)))
    (map_mono (comap_mono hUX)) hVne hYne hNY hfixV
  exact ⟨W₀,hZW,hWU,hWX,hmax,hON,hVne,hYne,hNY,hVe,hVN,hfixV,hb,hsol⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
