module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.FixedCosets
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.MaximalNormalizer

/-!
# The prepared unitary maximal-W quotient

After the same extension's odd outer degree, retain the marked short root,
long root, ambient Sylow and entire q-element fixed line from the first
fixed-coset argument. If C_{N_G(L)}(t) is proper in C_G(t), construct the
source maximal W and apply full I.8.5 in N_{C_G(t)}(W)/W. All quotient maps
and relative normalizers are literal; both orientations, degree-two rows
and q=4 are retained.

The final odd-core/perfect-actor contradiction, outer transfer and ambient
order comparison remain required. Source: Aschbacher–Smith F.4.42, p.296.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The original prepared row supplies the full maximal-W I.8.5 application.
Only the already explicit odd-outer-degree premise is retained. -/
theorem Preparation.unitary_short_maximal_section_of_odd_outer
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
      let f := QuotientGroup.mk' (W.subgroupOf N)
      let V := (U₀.subgroupOf N).map f
      let Y := (X.subgroupOf N).map f
      V ≠ ⊥ ∧ Y ≠ ⊤ ∧ normalizer (V : Set (N ⧸ W.subgroupOf N)) = Y ∧
      IsElementaryAbelian 2 V ∧
      ∃ hnormal : (V.subgroupOf Y).Normal, letI := hnormal;
      (∀ v ∈ V, v ≠ 1 → ∃! q : (N ⧸ W.subgroupOf N) ⧸ Y, v • q = q) ∧
      (let K := normalClosure (V : Set (N ⧸ W.subgroupOf N))
       (Nat.card V = 2 ∧ pPrimeCore 2 K ⊔ V.subgroupOf K = ⊤) ∨
         (IsQuasisimple K ∧ BenderSuzuki.IsSimpleBenderGroup (K ⧸ center K) ∧
           Y.comap K.subtype = normalizer (V.subgroupOf K : Set K) ∧
           BenderSuzuki.IsBorelSubgroup (Y.comap K.subtype) ∧
           ∃ S : Sylow 2 K, (S : Subgroup K) ≤ Y.comap K.subtype ∧
             V.subgroupOf K = (omega₁ S (p := 2)).map (S : Subgroup K).subtype)) ∧
      Group.IsSolvable (Y ⧸ centralizer (V.subgroupOf Y : Set Y))) := by
  obtain ⟨hmgt,hn,t,ht,z,hz,hzc,U,hU,hUV,hUc,_,_,_,htU,
      hfix,_,_,hNU,hV,P,hPX,hzP,hPcentral⟩ :=
    d.unitary_short_fixed_cosets_sylow_of_odd_outer h hH hp m hm hc r hodd
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
  exact ChapterF.UnitarySource.maximal_normalizer_section X U₀ (zpowers t₀)
    hX hUX (zpowers_le.mpr htU₀) (zpowers_le.mpr htcenter) hNU
    P hPX (j z) hzP hPcentral hfix

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
