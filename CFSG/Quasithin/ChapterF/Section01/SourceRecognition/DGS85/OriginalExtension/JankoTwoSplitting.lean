module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoCartanActors
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# Simultaneous splitting above the reduced Hall–Janko pair

The source cubic and its inverting outer involution generate an actual
order-six complement to the original Borel two-core. Disjointness is
proved in the group: the odd powers meet the two-core trivially, while
all words in the other coset leave the reduced Borel. The complement is
identified with S₃ through the literal original Borel quotient map.
The same involution complements each normal reduced endpoint and the
whole reduced Borel, so the three extensions split simultaneously.

Source: DGS, Groups and Graphs (1985), (15.3), printed pp.229–231.
The reduced parabolic comparison remains explicit. The endpoint action
relations and the order-twelve product are still required to identify
these split extensions with the Aut(J₂) parabolics.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo

private theorem involution_powers {A : Type*} [Group A]
    (x : A) (hx : x^2=1) (hx1 : x≠1) {y : A} (hy : y∈zpowers x) :
    y=1 ∨ y=x := by
  classical
  have ho : orderOf x=2 := orderOf_eq_prime hx hx1
  have hf : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,hx⟩
  rw [hf.mem_zpowers_iff_mem_range_orderOf,ho] at hy
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hy
  have hn2 := Finset.mem_range.mp hn
  have hn' : n=0 ∨ n=1 := by omega
  rcases hn' with rfl | rfl
  · exact Or.inl (by simpa using he.symm)
  · exact Or.inr (by simpa using he.symm)

private theorem index_two_complement {A : Type*} [Group A] [Finite A]
    (N : Subgroup A) (hi : N.index=2) (x : A) (hx : x^2=1) (hout : x∉N) :
    IsComplement' N (zpowers x) := by
  have hx1 : x≠1 := fun he => hout (he ▸ N.one_mem)
  apply isComplement'_of_card_mul_and_disjoint
  · rw [Nat.card_zpowers,orderOf_eq_prime hx hx1,←hi]
    exact N.card_mul_index
  · apply disjoint_def.mpr
    intro y hyN hyx
    rcases involution_powers x hx hx1 hyx with rfl | rfl
    · rfl
    · exact (hout hyN).elim

private theorem cubic_involution_complement {A : Type*} [Group A] [Finite A]
    (R N : Subgroup A) (hRN : R≤N)
    (hR : Nat.card R=128) (hA : Nat.card A=768)
    (k x : A) (hk : orderOf k=3) (hkN : k∈N)
    (hx : x^2=1) (hxN : x∉N) (hinv : x*k*x⁻¹=k⁻¹) :
    IsComplement' (zpowers k ⊔ zpowers x) R := by
  have hkN' : zpowers k≤N := zpowers_le.mpr hkN
  have hxk : x∉zpowers k := fun hxk => hxN (hkN' hxk)
  have hnorm : x∈normalizer (zpowers k : Set A) := by
    rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    change zpowers (x*k*x⁻¹)=zpowers k
    rw [hinv,zpowers_inv]
  have hC : Nat.card (zpowers k ⊔ zpowers x : Subgroup A)=6 := by
    rw [card_sup_zpowers_of_normalizing_involution _ _ hx hxk hnorm,
      Nat.card_zpowers,hk]
  have hdisj : Disjoint (zpowers k) R := disjoint_of_coprime_natCard (by
    rw [Nat.card_zpowers,hk,hR]; decide)
  have hx1 : x≠1 := fun he => hxN (he ▸ N.one_mem)
  apply isComplement'_of_card_mul_and_disjoint (by rw [hC,hR,hA])
  apply disjoint_def.mpr
  intro y hyC hyR
  have hyp : y∈(zpowers k : Set A)*(zpowers x : Set A) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.mpr hnorm)]
    exact hyC
  obtain ⟨u,hu,v,hv,rfl⟩ := hyp
  rcases involution_powers x hx hx1 hv with rfl | rfl
  · change u*1∈R at hyR
    change u*1=1
    rw [mul_one] at hyR ⊢
    exact disjoint_def.mp hdisj hu hyR
  · exact (hxN ((N.mul_mem_cancel_left (hkN' hu)).mp (hRN hyR))).elim

open SuzukiContainment GreenBook
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Every original Borel involution outside B₀ splits both original
endpoint extensions, with their literal normal reduced subgroups. -/
theorem original_outer_endpoint_complement
    (h : HypothesisF11 L S) (i : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (hne : S≠reducedSylow L S) (x : commonBorel L S)
    (hx : x^2=1) (hxN : (x:G)∉commonBorel L (reducedSylow L S)) (j : Fin 2) :
    IsComplement' ((parabolic L (reducedSylow L S) j).subgroupOf (parabolic L S j))
      (zpowers (inclusion (commonBorel_le_parabolic j) x)) := by
  let := h.finite_parabolic j
  apply index_two_complement
  · exact (parabolic_extension_index h j).trans (original_borel_index_two_of_ne h i e hne)
  · simpa only [←map_pow,map_one] using congrArg (inclusion (commonBorel_le_parabolic j)) hx
  · intro he
    apply hxN
    rw [←reduced_parabolic_inf_borel h j]
    exact ⟨he,x.property⟩

/-- The same involution splits the entire reduced Borel, including its
odd factor; this is a complement to B₀, distinct from O₂(B). -/
theorem original_outer_borel_complement
    (h : HypothesisF11 L S) (i : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (hne : S≠reducedSylow L S) (x : commonBorel L S)
    (hx : x^2=1) (hxN : (x:G)∉commonBorel L (reducedSylow L S)) :
    IsComplement' ((commonBorel L (reducedSylow L S)).subgroupOf (commonBorel L S))
      (zpowers x) := by
  let := h.finite_commonBorel
  exact index_two_complement _ (original_borel_index_two_of_ne h i e hne) x hx hxN

/-- The constructed Cartan actors generate a complement to the original
O₂(B). No original Borel model or splitting is assumed. -/
theorem original_borel_cubic_involution_complement
    (h : HypothesisF11 L S) (i : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (b : commonBorel L (reducedSylow L S) ≃* HallJanko.j2Model.toMarking.B)
    (hne : S≠reducedSylow L S) (k x : commonBorel L S)
    (hk : orderOf k=3) (hkN : (k:G)∈commonBorel L (reducedSylow L S))
    (hx : x^2=1) (hxN : (x:G)∉commonBorel L (reducedSylow L S))
    (hinv : x*k*x⁻¹=k⁻¹) :
    IsComplement' (zpowers k ⊔ zpowers x) (pCore 2 (commonBorel L S)) := by
  let := h.finite_commonBorel
  apply cubic_involution_complement _
    ((commonBorel L (reducedSylow L S)).subgroupOf (commonBorel L S))
    _ _ (original_borel_card_of_ne h i e b hne) k x hk hkN hx hxN hinv
  · intro z hz
    exact (show reducedSylow L S≤commonBorel L (reducedSylow L S) from le_sup_right)
      (mem_map_of_mem (commonBorel L S).subtype hz)
  · have hh := reduced_sylow_card h i e
    change Nat.card ((pCore 2 (commonBorel L S)).map (commonBorel L S).subtype)=128 at hh
    rwa [card_map_of_injective (commonBorel L S).subtype_injective] at hh

private theorem borel_actors {Y : Type*} [Group Y]
    (P B₀ B : Subgroup Y) (hB : B₀≤B)
    (hs : ∃ k x : P, orderOf k=3 ∧ (k:Y)∈B₀ ∧
      x^2=1 ∧ (x:Y)∈B ∧ (x:Y)∉B₀ ∧ x*k*x⁻¹=k⁻¹) :
    ∃ k x : B, orderOf k=3 ∧ (k:Y)∈B₀ ∧
      x^2=1 ∧ (x:Y)∉B₀ ∧ x*k*x⁻¹=k⁻¹ := by
  obtain ⟨k,x,hk,hkB,hx,hxB,hxN,hinv⟩ := hs
  let kB : B := ⟨k,hB hkB⟩
  let xB : B := ⟨x,hxB⟩
  have hk3 : orderOf kB=3 :=
    (orderOf_coe kB).symm.trans ((orderOf_coe k).trans hk)
  have hx2 : xB^2=1 := Subtype.ext (congrArg (fun y : P => (y:Y)) hx)
  have hinvB : xB*kB*xB⁻¹=kB⁻¹ :=
    Subtype.ext (congrArg (fun y : P => (y:Y)) hinv)
  exact ⟨kB,xB,hk3,hkB,hx2,hxN,hinvB⟩

/-- The complement is S₃ by the actual quotient map, not by order six
alone. Both endpoints and the full Borel use the same outer involution. -/
theorem exists_original_simultaneous_complements
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (b : commonBorel L (reducedSylow L S) ≃* HallJanko.j2Model.toMarking.B)
    (hne : S≠reducedSylow L S) :
    ∃ k x : commonBorel L S,
      orderOf k=3 ∧ (k:G)∈commonBorel L (reducedSylow L S) ∧
      x^2=1 ∧ (x:G)∉commonBorel L (reducedSylow L S) ∧ x*k*x⁻¹=k⁻¹ ∧
      IsComplement' (zpowers k ⊔ zpowers x) (pCore 2 (commonBorel L S)) ∧
      Nonempty ((zpowers k ⊔ zpowers x : Subgroup (commonBorel L S)) ≃* Equiv.Perm (Fin 3)) ∧
      IsComplement' ((commonBorel L (reducedSylow L S)).subgroupOf (commonBorel L S))
        (zpowers x) ∧
      ∀ r : Fin 2, IsComplement'
        ((parabolic L (reducedSylow L S) r).subgroupOf (parabolic L S r))
        (zpowers (inclusion (commonBorel_le_parabolic r) x)) := by
  have hs : ∃ k x : parabolic L S j, orderOf k=3 ∧
      (k:G)∈commonBorel L (reducedSylow L S) ∧ x^2=1 ∧
      (x:G)∈commonBorel L S ∧ (x:G)∉commonBorel L (reducedSylow L S) ∧
      x*k*x⁻¹=k⁻¹ := by
    obtain ⟨k,x,hk,hkB,hx,hxB,hxN,_,_,hinv,_⟩ :=
      exists_original_borel_outer_cubic_relations h i j e f hne
    exact ⟨k,x,hk,hkB,hx,hxB,hxN,hinv⟩
  obtain ⟨kB,xB,hk3,hkB,hx2,hxN,hinvB⟩ := borel_actors _ _ _ (reduced_commonBorel_le h) hs
  have hC := original_borel_cubic_involution_complement h i e b hne
    kB xB hk3 hkB hx2 hxN hinvB
  obtain ⟨q⟩ := original_borel_quotient_of_ne h i e b hne
  exact ⟨kB,xB,hk3,hkB,hx2,hxN,hinvB,hC,
    ⟨hC.QuotientMulEquiv.symm.trans q⟩,
    original_outer_borel_complement h i e hne xB hx2 hxN,
    original_outer_endpoint_complement h i e hne xB hx2 hxN⟩

private theorem ambient_complement {Y : Type*} [Group Y]
    (N P : Subgroup Y) (hNP : N≤P) (x : P)
    (hc : IsComplement' (N.subgroupOf P) (zpowers x)) :
    N ⊔ zpowers (x:Y)=P ∧ Disjoint N (zpowers (x:Y)) := by
  have hs := congrArg (fun K : Subgroup P => K.map P.subtype) hc.sup_eq_top
  have hi := congrArg (fun K : Subgroup P => K.map P.subtype) hc.disjoint.eq_bot
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hNP,MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype] at hs
  rw [Subgroup.map_inf _ _ _ P.subtype_injective,map_subgroupOf_eq_of_le hNP,
    MonoidHom.map_zpowers,Subgroup.map_bot] at hi
  exact ⟨hs,disjoint_iff.mpr hi⟩

private theorem generators_transport {Y : Type*} [Group Y]
    (B₀ B : Subgroup Y) (P₀ P : Fin 2 → Subgroup Y)
    (hB : B₀≤B) (hP : ∀ r, P₀ r≤P r) (hBP : ∀ r, B≤P r)
    (hs : ∃ k x : B, orderOf k=3 ∧ (k:Y)∈B₀ ∧ x^2=1 ∧ (x:Y)∉B₀ ∧
      x*k*x⁻¹=k⁻¹ ∧ IsComplement' (zpowers k ⊔ zpowers x) (pCore 2 B) ∧
      Nonempty ((zpowers k ⊔ zpowers x : Subgroup B) ≃* Equiv.Perm (Fin 3)) ∧
      IsComplement' (B₀.subgroupOf B) (zpowers x) ∧
      ∀ r : Fin 2, IsComplement' ((P₀ r).subgroupOf (P r))
        (zpowers (inclusion (hBP r) x))) :
    ∃ k x : B, orderOf k=3 ∧ (k:Y)∈B₀ ∧ x^2=1 ∧ (x:Y)∉B₀ ∧
      x*k*x⁻¹=k⁻¹ ∧ IsComplement' (zpowers k ⊔ zpowers x) (pCore 2 B) ∧
      Nonempty ((zpowers k ⊔ zpowers x : Subgroup B) ≃* Equiv.Perm (Fin 3)) ∧
      (B₀ ⊔ zpowers (x:Y)=B ∧ Disjoint B₀ (zpowers (x:Y))) ∧
      ∀ r : Fin 2, P₀ r ⊔ zpowers (x:Y)=P r ∧ Disjoint (P₀ r) (zpowers (x:Y)) := by
  obtain ⟨k,x,hk,hkB,hx,hxB,hinv,hC,he,hB',hP'⟩ := hs
  exact ⟨k,x,hk,hkB,hx,hxB,hinv,hC,he,
    ambient_complement B₀ B hB x hB',
    fun r => ambient_complement (P₀ r) (P r) (hP r) (inclusion (hBP r) x) (hP' r)⟩

/-- The original three groups are generated by their literal reduced
subgroups and one common outer involution, with trivial intersection.
The order-six complement remains in the full original Borel. -/
theorem exists_original_simultaneous_generators
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (b : commonBorel L (reducedSylow L S) ≃* HallJanko.j2Model.toMarking.B)
    (hne : S≠reducedSylow L S) :
    ∃ k x : commonBorel L S,
      orderOf k=3 ∧ (k:G)∈commonBorel L (reducedSylow L S) ∧
      x^2=1 ∧ (x:G)∉commonBorel L (reducedSylow L S) ∧ x*k*x⁻¹=k⁻¹ ∧
      IsComplement' (zpowers k ⊔ zpowers x) (pCore 2 (commonBorel L S)) ∧
      Nonempty ((zpowers k ⊔ zpowers x : Subgroup (commonBorel L S)) ≃* Equiv.Perm (Fin 3)) ∧
      (commonBorel L (reducedSylow L S) ⊔ zpowers (x:G)=commonBorel L S ∧
        Disjoint (commonBorel L (reducedSylow L S)) (zpowers (x:G))) ∧
      ∀ r : Fin 2, parabolic L (reducedSylow L S) r ⊔ zpowers (x:G)=parabolic L S r ∧
        Disjoint (parabolic L (reducedSylow L S) r) (zpowers (x:G)) := by
  exact generators_transport _ _ _ _ (reduced_commonBorel_le h)
    (reduced_parabolic_le h) commonBorel_le_parabolic
    (exists_original_simultaneous_complements h i j e f b hne)

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
