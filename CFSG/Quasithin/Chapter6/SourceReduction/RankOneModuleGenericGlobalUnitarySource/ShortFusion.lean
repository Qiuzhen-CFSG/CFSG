module
public import Theory.GroupTheory.WeakClosureQuotientFusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.AmbientThompson

/-!
# Ambient fusion on the original unitary short-line quotient

Burnside's weak-closure correction is performed inside N_{C_G(t)}(U).
Its normal quotient has exactly the whole q-element line as kernel.
On the image of O₂(L), any simultaneous ambient conjugation of a set of
vectors back into this image is induced by an element of the same line
normalizer which also normalizes the original L. In particular this holds
for every configuration in the q² long-root module. All witnesses and
quotient maps are those of the original short-quotient construction.

Source: Aschbacher–Smith F.4.42, printed pp.295–296, using A.1.35.
The common-centralizer bound needed for unique fixed cosets remains a
separate ambient step; fusion alone does not prove that bound.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open UnitaryCompletion
namespace UnitarySource
variable {G : Type*} [Group G] (L : Subgroup G) (t : L)

/-- The faithful embedding of the literal ambient line normalizer into G. -/
def shortLineAmbientEmbedding (U : Subgroup (centralizer ({t} : Set L))) :
    shortLineNormalizer L t U →* G :=
  (centralizer ({t.val} : Set G)).subtype.comp (shortLineNormalizer L t U).subtype

theorem shortLineAmbientEmbedding_injective
    (U : Subgroup (centralizer ({t} : Set L))) :
    Function.Injective (shortLineAmbientEmbedding L t U) := by
  intro x y he
  exact Subtype.ext (Subtype.ext he)

/-- An abelian core containing t and the entire line lies in the original
line normalizer, so Burnside correction can be carried out there. -/
theorem core_le_shortLineAmbientEmbedding_range
    (U : Subgroup (centralizer ({t} : Set L))) (Q : Subgroup G)
    (habel : Q ≤ centralizer (Q : Set G)) (ht : t.val ∈ Q)
    (hU : ∀ u ∈ U, u.val.val ∈ Q) :
    Q ≤ (shortLineAmbientEmbedding L t U).range := by
  intro x hx
  have hxt : x ∈ centralizer ({t.val} : Set G) :=
    mem_centralizer_singleton_iff.mpr (habel ht x hx)
  let a : centralizer ({t.val} : Set G) := ⟨x,hxt⟩
  have ha : a ∈ shortLineNormalizer L t U := by
    apply Subgroup.centralizer_le_normalizer
    rintro _ ⟨u,hu,rfl⟩
    apply Subtype.ext
    exact habel hx u.val.val (hU u hu)
  exact ⟨⟨a,ha⟩,rfl⟩

end UnitarySource

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- Simultaneous fusion on the full core image in the literal line quotient.
The corrected element stays in the same ambient line normalizer and
normalizes L; the whole original line is retained in the kernel. -/
theorem Preparation.unitary_short_line_quotient_set_fusion
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (t : L) (ht : t.val ∈ L.pCoreIn 2)
    (U : Subgroup (centralizer ({t} : Set L)))
    (hU : ∀ u ∈ U, u.val.val ∈ L.pCoreIn 2)
    (s : Set (UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U))
    (hs : s ⊆ ((L.pCoreIn 2).comap (UnitarySource.shortLineAmbientEmbedding L t U)).map
      (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U)))
    (g : UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U)
    (hgs : ∀ x ∈ s, g*x*g⁻¹ ∈
      ((L.pCoreIn 2).comap (UnitarySource.shortLineAmbientEmbedding L t U)).map
        (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U))) :
    ∃ a : UnitarySource.shortLineNormalizer L t U,
      a.val.val ∈ normalizer (L : Set G) ∧ ∀ x ∈ s,
        QuotientGroup.mk' (UnitarySource.shortLineKernel L t U) a * x *
          (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U) a)⁻¹ = g*x*g⁻¹ := by
  let Q := L.pCoreIn 2
  let j := UnitarySource.shortLineAmbientEmbedding L t U
  have hJ := d.unitary_thompson h hH hp m hm hc
  have hQP : Q ≤ (T : Subgroup G) := by
    change L.pCoreIn 2 ≤ (T : Subgroup G)
    rw [←hJ]
    exact sSup_le fun _ hA => hA.1
  have hw : ∀ g : G, Q.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      g ∈ normalizer (Q : Set G) := by
    intro g hg
    change (L.pCoreIn 2).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) at hg
    change g ∈ normalizer (L.pCoreIn 2 : Set G)
    rw [←hJ] at hg ⊢
    exact maxJ_weakly_closed T g hg
  have habel : Q ≤ centralizer (Q : Set G) :=
    (d.unitary_core_centralizer h hH hp m hm hc).ge
  have hQj : Q ≤ j.range := UnitarySource.core_le_shortLineAmbientEmbedding_range L t U Q habel ht hU
  have hker : (UnitarySource.shortLineKernel L t U).map j ≤ Q := by
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨u,hu,he⟩ := ha
    have hh := congrArg (fun x : centralizer ({t.val} : Set G) => x.val) he
    change u.val.val = j a at hh
    exact hh ▸ hU u hu
  obtain ⟨a,ha,he⟩ := Sylow.WeakClosure.quotient_set_fusion T Q hQP hw habel j
    (UnitarySource.shortLineAmbientEmbedding_injective L t U) hQj
    (UnitarySource.shortLineKernel L t U) hker s hs g hgs
  have hnorm : normalizer (Q : Set G) = normalizer (L : Set G) := by
    change normalizer (L.pCoreIn 2 : Set G) = normalizer (L : Set G)
    rw [←hJ]
    exact d.unitary_thompson_normalizer h hH hp m hm hc
  exact ⟨a,hnorm ▸ ha,he⟩

/-- The same prepared short-root quotient has its marked nonzero-vector
orbit and simultaneous ambient fusion controlled inside the original
line normalizer by elements normalizing L. No new fusion premise is
required from the prepared row. -/
theorem Preparation.unitary_short_root_ambient_quotient_fusion
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 ∧
      f z ≠ 1 ∧ (∀ v ∈ V.map f, v ≠ 1 →
        ∃ a ∈ primeToResidual 2 (centralizer ({t} : Set L)),
          f a * f z * (f a)⁻¹ = v) ∧
      ∀ (s : Set (UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U)),
        s ⊆ V.map f →
        ∀ g : UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U,
          (∀ x ∈ s, g*x*g⁻¹ ∈ V.map f) →
          ∃ a : UnitarySource.shortLineNormalizer L t U,
            a.val.val ∈ normalizer (L : Set G) ∧ ∀ x ∈ s,
              QuotientGroup.mk' (UnitarySource.shortLineKernel L t U) a * x *
                (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U) a)⁻¹ = g*x*g⁻¹ := by
  obtain ⟨hm',hn,t,ht,z,hz,U,hV,hVQ,hVc,hUc,hindex,hUV,hU,htU,hfusion⟩ :=
    d.unitary_short_root_quotient_orbits_with_core h hH hp m hm hc
  let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
  let f := UnitarySource.shortLineQuotientMap L t U hU
  have hker : f.ker = U := UnitarySource.shortLineQuotientMap_ker L t U hU
  let : IsElementaryAbelian 2 V := hV
  have hcV : Nat.card (V.map f) = (2^m)^2 := by
    rw [←relIndex_ker,hker]
    exact hindex
  have hfusion := hfusion f hker.ge
  have hzne : f z ≠ 1 := by
    let : Nontrivial (V.map f) := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcV]
      exact Nat.one_lt_pow (by decide) (Nat.one_lt_pow (by omega) (by decide)))
    obtain ⟨v,hv⟩ := exists_ne (1 : V.map f)
    have hvne : v.val ≠ 1 := fun he => hv (Subtype.ext he)
    obtain ⟨a,ha,he⟩ := hfusion v.val v.property hvne
    intro hzero
    rw [hzero,mul_one,mul_inv_cancel] at he
    exact hvne he.symm
  have htkill : f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 :=
    MonoidHom.mem_ker.mp (hker.ge (htU.le (mem_zpowers _)))
  refine ⟨hm',hn,t,ht,z,hz,U,hU,hUc,hker,IsElementaryAbelian.map f,hcV,htU,htkill,hzne,hfusion,?_⟩
  have hUQ : ∀ u ∈ U, u.val.val ∈ L.pCoreIn 2 := by
    intro u hu
    exact hVQ (mem_map_of_mem L.subtype
      (mem_map_of_mem (centralizer ({t} : Set L)).subtype (hUV hu)))
  have htQ : t.val ∈ L.pCoreIn 2 := hUQ _ (htU.le (mem_zpowers _))
  have hmap : V.map f ≤
      ((L.pCoreIn 2).comap (UnitarySource.shortLineAmbientEmbedding L t U)).map
        (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U)) := by
    rintro v ⟨w,hw,rfl⟩
    refine ⟨UnitarySource.shortLineNormalizerMap L t U hU w,?_,rfl⟩
    exact hVQ (mem_map_of_mem L.subtype
      (mem_map_of_mem (centralizer ({t} : Set L)).subtype hw))
  intro s hs g hgs
  exact d.unitary_short_line_quotient_set_fusion h hH hp m hm hc t htQ U hUQ s
    (hs.trans hmap) g (fun x hx => hmap (hgs x hx))


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
