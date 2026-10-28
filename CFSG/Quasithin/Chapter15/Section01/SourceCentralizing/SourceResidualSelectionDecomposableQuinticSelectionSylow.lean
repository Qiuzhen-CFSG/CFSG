module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionDisplacement

/-!
# The actual marked Sylow centralizer for a diagonal partner module

When the partner module has order four, it is a full diagonal between the
original two Thompson planes. An element of T fixing the first plane also
preserves the second plane and the diagonal, and hence fixes all of E.
Consequently the marked centralizer C_T(Z1) is C_T(E), which is normal in T.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem fixes_diagonal_complement
    {X : Type*} [CommGroup X]
    (A B U : Subgroup X) (hAB : A⊔B=⊤) (hUA : U⊔A=⊤)
    (hd : Disjoint U B) (α : MulAut X)
    (hU : ∀u∈U, α u∈U) (hB : ∀b∈B, α b∈B)
    (hA : ∀a∈A, α a=a) : ∀x:X, α x=x := by
  have hfixU : ∀u∈U, α u=u := by
    intro u hu
    obtain ⟨a,ha,b,hb,he⟩ := mem_sup.mp (show u∈A⊔B from hAB ▸ mem_top u)
    have he' : α u*u⁻¹=α b*b⁻¹ := by
      rw [←he,map_mul,hA a ha,mul_inv_rev]
      calc
        _=(a*a⁻¹)*(α b*b⁻¹) := by ac_rfl
        _=_ := by rw [mul_inv_cancel,one_mul]
    apply mul_inv_eq_one.mp
    exact disjoint_def.mp hd (U.mul_mem (hU u hu) (U.inv_mem hu))
      (he' ▸ B.mul_mem (hB b hb) (B.inv_mem hb))
  intro x
  obtain ⟨u,hu,a,ha,rfl⟩ := mem_sup.mp (show x∈U⊔A from hUA ▸ mem_top x)
  rw [map_mul,hfixU u hu,hA a ha]

omit [Finite G] in
private theorem centralizes_diagonal_complement
    (E A B U : Subgroup G) [IsElementaryAbelian 2 E]
    (hAE : A≤E) (hBE : B≤E) (hUE : U≤E)
    (hAB : A⊔B=E) (hUA : U⊔A=E) (hd : Disjoint U B)
    (g : G) (hgn : g∈normalizer (E : Set G))
    (hU : g∈normalizer (U : Set G)) (hB : g∈normalizer (B : Set G))
    (hA : g∈centralizer (A : Set G)) : g∈centralizer (E : Set G) := by
  let α : MulAut E := E.normalizerMonoidHom ⟨g,hgn⟩
  have hAB' : A.subgroupOf E⊔B.subgroupOf E=⊤ := by
    rw [←subgroupOf_sup hAE hBE,hAB,subgroupOf_self]
  have hUA' : U.subgroupOf E⊔A.subgroupOf E=⊤ := by
    rw [←subgroupOf_sup hUE hAE,hUA,subgroupOf_self]
  have hd' : Disjoint (U.subgroupOf E) (B.subgroupOf E) := by
    apply disjoint_def.mpr
    intro x hx hy
    exact Subtype.ext (disjoint_def.mp hd hx hy)
  have hn (D : Subgroup G) (hD : g∈normalizer (D : Set G)) :
      ∀x∈D.subgroupOf E, α x∈D.subgroupOf E := by
    intro x hx
    exact (mem_normalizer_iff.mp hD x).mp hx
  have hf : ∀a∈A.subgroupOf E, α a=a := by
    intro a ha
    apply Subtype.ext
    change g*(a:G)*g⁻¹=(a:G)
    rw [←hA a ha,mul_inv_cancel_right]
  have hall := fixes_diagonal_complement (A.subgroupOf E) (B.subgroupOf E)
    (U.subgroupOf E) hAB' hUA' hd' α (hn U hU) (hn B hB) hf
  intro x hx
  have he := congrArg Subtype.val (hall ⟨x,hx⟩)
  change g*x*g⁻¹=x at he
  have hh := congrArg (fun y:G => y*g) he
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh.symm

/-- In the actual order-four partner branch, the original marked Sylow
centralizer equals the full Thompson fixed subgroup's centralizer and is normal. -/
theorem PreparedChosenModule.decomposable_five_partner_four_marked_sylow_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc)=4 →
      let E := thompsonFixed T V
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      (T : Subgroup G)⊓centralizer (Z₁ : Set G)=
        (T : Subgroup G)⊓centralizer (E : Set G) ∧
      (((T : Subgroup G)⊓centralizer (Z₁ : Set G)).subgroupOf (T : Subgroup G)).Normal := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  let Uc := localModule T Mc
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  obtain ⟨_,hd₂,hjoin₁,_,_⟩ := h.decomposable_five_partner_four_diagonal_displacement
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hUE : Uc≤E := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2
  have hZ₁ : Z₁≤E := inf_le_right
  have hZ₂ : Z₂≤E := inf_le_right
  have hMcC : Mc∈maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G)≤Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hTU : (T : Subgroup G)≤normalizer (Uc : Set G) :=
    hTMc.trans (le_normalizer_conjugateSpanBy _ _)
  have hTE : (T : Subgroup G)≤normalizer (E : Set G) :=
    (le_inf (hM.1.2.trans h.normalized)
      ((ChapterB.le_normalizer_thompsonJ _ _).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have he : (T : Subgroup G)⊓centralizer (Z₁ : Set G)=
      (T : Subgroup G)⊓centralizer (E : Set G) := by
    apply le_antisymm
    · intro t ht
      refine ⟨ht.1,?_⟩
      have hn₂ := (s.thompson_normalized ⟨ht.1,s.centralizer_le_stabilizer ht⟩).2
      exact centralizes_diagonal_complement E Z₁ Z₂ Uc hZ₁ hZ₂ hUE
        s.thompson_split.symm hjoin₁ hd₂ t (hTE ht.1) (hTU ht.1) hn₂ ht.2
    · exact inf_le_inf_left _ (centralizer_le hZ₁)
  refine ⟨he,?_⟩
  rw [he]
  exact normal_subgroupOf_of_le_normalizer
    ((le_inf (T : Subgroup G).le_normalizer
      (hTE.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf)

end CFSG.Quasithin.Chapter15.Section01
