module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointThreeRank
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockPoint
public import Theory.GroupTheory.PCoreImage
public import Theory.ElementaryAbelian.Injective

/-!
# The original singular-point residual and its Sylow three-subgroups

Restrict the marked C_L(z) action to its actual two-residual L₁. Residual
image transport identifies the image with the two alternating four-block
factors. The action kernel is L₁ intersect O₂(L), whereas the composite to
the displayed E₉ has kernel O₂(L₁). These kernels are kept distinct.

The same map identifies every original Sylow three-subgroup of L₁ with
E₉. Its image under H -> H/O₂(H) remains elementary of order nine, and
the quotient projection is injective on that subgroup. The residual
centralizer argument uses this original Sylow image to exclude inverted
cubic elements. Vanishing of C_V(L) and T-invariance of the chosen point
remain the explicit earlier-source inputs.

Source: Aschbacher--Smith, proof of 12.6.26, printed pp.831--832.
-/

public section
open Subgroup Theory.GroupTheory
open BinaryPermutation BinaryPermutation.TerminalOrthogonal
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis K T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The original two-residual has its actual alternating block action,
with both the action kernel and the E₉ quotient kernel identified. -/
theorem SourceHypothesis.original_point_residual_map
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G)) :
    ∃ (r : alternatingGroup (Fin 8))
      (f : (D.fullSetup hZ T z).L₁ →* FourBlockResidual.R),
      Function.Surjective f ∧
      (∀ c, (f c).val = r.val *
        (D.groupEquiv (QuotientGroup.mk' (conjugation L V S.chosen.normalizes).ker
          ⟨c.val, (show (D.fullSetup hZ T z).L₁ ≤ L from
            (map_subtype_le _).trans inf_le_left) c.property⟩)).val * r.val⁻¹) ∧
      f.ker = (L.pCoreIn 2).subgroupOf (D.fullSetup hZ T z).L₁ ∧
      (FourBlockResidual.quotientMap.comp f).ker = pCore 2 (D.fullSetup hZ T z).L₁ := by
  let E := D.fullSetup hZ T z
  let C := L ⊓ E.Gz
  obtain ⟨r, a, ha, hformula, hk⟩ := S.original_point_stabilizer_map D hZ z hz hTz
  have hEC : E.L₁ ≤ C := map_subtype_le _
  let j : E.L₁ →* C := inclusion hEC
  let b : E.L₁ →* FourBlockResidual.S8 := FourBlockResidual.P.subtype.comp (a.comp j)
  have hsub : E.L₁.subgroupOf C = pResidual 2 C :=
    comap_map_eq_self_of_injective C.subtype_injective _
  have hrange : b.range = FourBlockResidual.R := by
    have hj : j.range = E.L₁.subgroupOf C := by
      ext c
      constructor
      · rintro ⟨x,rfl⟩
        exact x.property
      · intro hc
        exact ⟨⟨c.val,hc⟩,rfl⟩
    change (FourBlockResidual.P.subtype.comp (a.comp j)).range = _
    rw [MonoidHom.range_comp,MonoidHom.range_comp,hj,hsub,
      map_pResidual_of_surjective 2 a ha]
    exact FourBlockPoint.intermediate_residual _ FourBlockResidual.R_le_P inf_le_right
  let f : E.L₁ →* FourBlockResidual.R := b.codRestrict _ (fun x => hrange ▸ (show b x ∈ b.range from ⟨x,rfl⟩))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨y,hy⟩ := hrange.ge x.property
    exact ⟨y,Subtype.ext hy⟩
  have hker : f.ker = (L.pCoreIn 2).subgroupOf E.L₁ := by
    ext x
    change f x = 1 ↔ x.val ∈ L.pCoreIn 2
    have he : f x = 1 ↔ a (j x) = 1 := by
      constructor
      · intro hh
        apply Subtype.ext
        exact congrArg (fun y : FourBlockResidual.R => y.val) hh
      · intro hh
        apply Subtype.ext
        exact congrArg (fun y : FourBlockResidual.P => y.val) hh
    rw [he,←MonoidHom.mem_ker,hk]
    rfl
  have hp : IsPGroup 2 f.ker := hker ▸ (isPGroup_pCoreIn 2 L).comap_subtype
  let q := FourBlockResidual.quotientMap.comp f
  have hpq : IsPGroup 2 q.ker := by
    change IsPGroup 2 (FourBlockResidual.quotientMap.comp f).ker
    rw [←MonoidHom.comap_ker,FourBlockResidual.quotientMap_ker]
    exact (IsElementaryAbelian.isPGroup 2 FourBlockResidual.E16).comap_of_ker_isPGroup f hp
  have hzero : pCore 2 FourBlockResidual.E9 = ⊥ := by
    have h2 : IsPGroup 2 (pCore 2 FourBlockResidual.E9) := pCore_isPGroup
    have h3 := (IsElementaryAbelian.isPGroup 3 FourBlockResidual.E9).to_subgroup
      (pCore 2 FourBlockResidual.E9)
    simpa only [inf_idem] using (h2.disjoint_of_coprime h3 (by decide)).eq_bot
  have hq := q.comap_pCore_of_ker_isPGroup
    (FourBlockResidual.quotientMap_surjective.comp hf) hpq
  rw [hzero,MonoidHom.comap_bot] at hq
  exact ⟨r,f,hf,fun x => hformula (j x),hker,hq⟩

/-- The same residual quotient map identifies the original two-core quotient
and every actual Sylow three-subgroup with the displayed E₉. -/
theorem SourceHypothesis.original_point_residual_quotient
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G)) :
    ∃ f : (D.fullSetup hZ T z).L₁ →* FourBlockResidual.E9,
      Function.Surjective f ∧ f.ker = pCore 2 (D.fullSetup hZ T z).L₁ ∧
      ∃ e : ((D.fullSetup hZ T z).L₁ ⧸ pCore 2 (D.fullSetup hZ T z).L₁) ≃*
          FourBlockResidual.E9,
        (∀ x, e (QuotientGroup.mk' _ x) = f x) ∧
        ∀ P : Sylow 3 (D.fullSetup hZ T z).L₁,
          ∃ s : P ≃* FourBlockResidual.E9, ∀ x : P, s x = f x.val := by
  obtain ⟨_,a,ha,_,_,hk⟩ := S.original_point_residual_map D hZ z hz hTz
  let f := FourBlockResidual.quotientMap.comp a
  have hf : Function.Surjective f := FourBlockResidual.quotientMap_surjective.comp ha
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  refine ⟨f,hf,hk,e,fun _ => rfl,?_⟩
  intro P
  have hp : (P.mapSurjective hf : Subgroup FourBlockResidual.E9) = ⊤ := by
    apply top_unique
    exact ((IsElementaryAbelian.isPGroup 3 FourBlockResidual.E9).to_subgroup ⊤).le_sylow_of_normal _
  let g := f.comp (P : Subgroup (D.fullSetup hZ T z).L₁).subtype
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨y,hy,he⟩ := hp.ge (mem_top x)
    exact ⟨⟨y,hy⟩,he⟩
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := (D.fullSetup hZ T z).L₁)).exists_card_eq
    rw [hk,hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact ⟨MulEquiv.ofBijective g
    ⟨injective_comp_subtype_of_coprime_ker f hcop P P.isPGroup',hg⟩,fun _ => rfl⟩

/-- Every original Sylow three-subgroup of L₁ is elementary of order nine. -/
theorem SourceHypothesis.original_point_residual_sylow
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    IsElementaryAbelian 3 P ∧ Nat.card P = 9 := by
  obtain ⟨_,_,_,_,_,hs⟩ := S.original_point_residual_quotient D hZ z hz hTz
  obtain ⟨e,_⟩ := hs P
  exact ⟨IsElementaryAbelian.of_injective e.toMonoidHom e.injective,
    (Nat.card_congr e.toEquiv).trans FourBlockResidual.E9_card⟩


/-- The same Sylow three-subgroup is still elementary of order nine in
H/O₂(H), and the actual ambient quotient is injective on its lift. -/
theorem SourceHypothesis.original_point_sylow_star
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    let A := (P : Subgroup (D.fullSetup hZ T z).L₁).map (D.fullSetup hZ T z).L₁.subtype
    IsElementaryAbelian 3 (Nonabelian.Setup.star H A) ∧
      Nat.card (Nonabelian.Setup.star H A) = 9 ∧
      Function.Injective ((QuotientGroup.mk' (pCore 2 H)).comp (A.subgroupOf H).subtype) := by
  let E := D.fullSetup hZ T z
  let A := (P : Subgroup E.L₁).map E.L₁.subtype
  obtain ⟨hP,hcard⟩ := S.original_point_residual_sylow D hZ z hz hTz P
  let := hP
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.map_subtype
  have hAH : A ≤ H := (map_subtype_le _).trans (fun x hx => hH.1.2 (Or.inl hx))
  let : IsElementaryAbelian 3 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  let q := QuotientGroup.mk' (pCore 2 H)
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hi := injective_comp_subtype_of_coprime_ker q hcop (A.subgroupOf H)
    (IsElementaryAbelian.isPGroup 3 (A.subgroupOf H))
  refine ⟨IsElementaryAbelian.map (A := A.subgroupOf H) q,?_,hi⟩
  change Nat.card ((A.subgroupOf H).map q) = 9
  let e := MulEquiv.ofBijective (q.subgroupMap (A.subgroupOf H))
    ⟨fun x y hh => hi (congrArg Subtype.val hh),q.subgroupMap_surjective _⟩
  rw [←Nat.card_congr e.toEquiv,Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv,
    card_map_of_injective E.L₁.subtype_injective]
  exact hcard


end CFSG.Quasithin.Chapter12.Section06
