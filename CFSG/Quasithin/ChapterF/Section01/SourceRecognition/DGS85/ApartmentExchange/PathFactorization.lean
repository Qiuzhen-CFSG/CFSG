module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourcePathRoots
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathBraidExchange

/-!
# Path radicals and the original universal Cartan

The original parabolic Sylows put both vertex two-cores in the whole Borel.
Transport through the injective universal endpoint maps and then along edges
shows that these two-cores fix all neighbors, without identifying them with
the full permutation kernels.

For an arbitrary nonempty path in the chosen reflection apartment, move its
first edge to the original marked edge. The preimage of its fixer is an
intermediate subgroup between K and B. The existing B=O₂(B)K factorization
therefore gives its own two-core times K. Conjugation transports the product
back to the literal path fixer. This supplies the half-path product in the
cubic exchange application, retaining both original endpoint maps.

Source: DGS, *Groups and Graphs* (1985), Part II, (3.2), (14.1),
printed pp.72,210--211; Aschbacher--Smith F.1.3, F.1.9, pp.260--262.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))

variable (n : ℕ) (hn : 1 < n)
variable (t : Bool → (reducedAmalgam L S).Universal)
variable (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
  base (Universal.cosetFamily (reducedAmalgam L S)) i)
variable (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
  base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
variable (htsq : ∀ i, t i * t i = 1)
variable (htnorm : ∀ i, t i ∈
  Subgroup.normalizer (cartan c : Set (reducedAmalgam L S).Universal))
variable (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S)) (n+1))
variable (hthick : ∀ i, ∃ z, (sourceGraph (reducedAmalgam L S)).Adj
  (base (Universal.cosetFamily (reducedAmalgam L S)) i) z ∧
  z ≠ base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
  z ≠ t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i))

variable (hodd : ∀ {a b} (q : (sourceGraph (reducedAmalgam L S)).Walk a b),
  q.IsPath → q.length = n+1 →
    Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) q)))

local notation "ρ" => pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick


private theorem core_range_image {A X : Type*} [Group A] [Group X]
    (f : A →* X) (hf : Function.Injective f) : f.range.pCoreIn 2=(pCore 2 A).map f := by
  unfold Subgroup.pCoreIn
  rw [← pCore_map_iso 2 (MonoidHom.ofInjective hf), Subgroup.map_map]
  rfl

include h in
/-- Both original endpoint two-cores lie in the whole universal Borel. -/
theorem universal_endpoint_core_le_middle (i : Bool) :
    (Universal.cosetFamily (reducedAmalgam L S) i).pCoreIn 2 ≤
      originalMiddle (reducedAmalgam L S) := by
  let A := reducedAmalgam L S
  have hL := inclusion_injective (commonBorel_le_parabolic (L := L)
    (S := reducedSylow L S) 0)
  have hR := inclusion_injective (commonBorel_le_parabolic (L := L)
    (S := reducedSylow L S) 1)
  have hinj := Universal.structureMap_injective A hL hR
  have hc (j : Fin 2) (x : parabolic L (reducedSylow L S) j) (hx : x∈pCore 2 _) :
      (x:G)∈commonBorel L (reducedSylow L S) :=
    (show reducedSylow L S ≤ commonBorel L (reducedSylow L S) from le_sup_right)
      ((reduced_hypothesis h).parabolic_core_le_S j ⟨x,hx,rfl⟩)
  cases i
  · change (Universal.left A).range.pCoreIn 2 ≤ _
    rw [core_range_image (Universal.left A) (Monoid.PushoutI.of_injective hinj false)]
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨⟨x,hc 0 x hx⟩,rfl⟩
  · change (Universal.right A).range.pCoreIn 2 ≤ _
    rw [core_range_image (Universal.right A) (Monoid.PushoutI.of_injective hinj true)]
    rintro _ ⟨x,hx,rfl⟩
    have he := congrArg (fun f => f ⟨(x:G),hc 1 x hx⟩) (Universal.compatible A)
    exact ⟨⟨x,hc 1 x hx⟩,he⟩

include h in
/-- Every actual vertex two-core fixes its neighbors; the full local permutation kernel may be larger. -/
theorem universal_vertex_core_fixes_neighbors
    (a b : SourceVertex (reducedAmalgam L S))
    (hab : (sourceGraph (reducedAmalgam L S)).Adj a b) :
    (MulAction.stabilizer (reducedAmalgam L S).Universal a).pCoreIn 2 ≤
      MulAction.stabilizer (reducedAmalgam L S).Universal b := by
  let A := reducedAmalgam L S
  obtain ⟨g,hga,hgb⟩ := RankTwo.incident_common_translate (Universal.cosetFamily A) hab.2
  rw [← hga, ← hgb, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_base, stabilizer_base,
    ← Subgroup.map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
  apply Subgroup.map_mono
  apply (universal_endpoint_core_le_middle h a.type).trans
  rw [originalMiddle, ← Universal.overlap_eq A
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))]
  cases b.type
  · exact inf_le_left
  · exact inf_le_right

include h n hn htfix htmove htsq htnorm htrans hthick in
/-- Every nonempty path in the actual apartment has fixer equal to its two-core times the same Cartan. -/
theorem apartment_path_factorization
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hpos : 0<p.length)
    (hT : ∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) :
    (pathFixer (X := (reducedAmalgam L S).Universal) p : Set (reducedAmalgam L S).Universal) =
      (pathRoot (X := (reducedAmalgam L S).Universal) p : Set (reducedAmalgam L S).Universal) * (cartan c : Set (reducedAmalgam L S).Universal) := by
  let A := reducedAmalgam L S
  let N := reflectionGroup c t
  have ha := pathRoots_a h c n hn t htfix htmove htsq htnorm htrans hthick
  have hb := pathRoots_b h c n hn t htfix htmove htsq htnorm htrans hthick
  have hlift := reflection_mem_apartmentGroup c ρ
  have hnormalizes := reflectionGroup_normalizes c t htnorm
  have hL := inclusion_injective (commonBorel_le_parabolic (L := L)
    (S := reducedSylow L S) 0)
  have hR := inclusion_injective (commonBorel_le_parabolic (L := L)
    (S := reducedSylow L S) 1)
  have hline := cartanApartment_noBranching A N (cartan c) ρ ha hb hlift
    (cartan_le c) hnormalizes le_rfl htsq hL hR
  have hadj : (sourceGraph A).Adj a (p.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using p.adj_getVert_succ hpos
  obtain ⟨g, hg, i, hga, hgb⟩ := cartanApartment_edge_coordinates A N ρ ha hb hlift hline
    (hT _ p.start_mem_support) (hT _ (p.getVert_mem_support 1)) hadj
  let e := (MulAut.conj g).toMonoidHom
  let F := (pathFixer (X := A.Universal) p).comap e
  have hFB : F ≤ originalMiddle A := by
    intro x hx
    have hxa := hx 0 (Nat.zero_le _)
    have hxb := hx 1 (by omega)
    simp only [SimpleGraph.Walk.getVert_zero] at hxa
    change (g*x*g⁻¹) • a=a at hxa
    change (g*x*g⁻¹) • p.getVert 1=p.getVert 1 at hxb
    have hleft : x∈Universal.cosetFamily A i := by
      rw [← stabilizer_base (Universal.cosetFamily A)]
      change x • base (Universal.cosetFamily A) i=base (Universal.cosetFamily A) i
      apply (MulAction.toPerm g).injective
      change g • (x • base (Universal.cosetFamily A) i)=g • base (Universal.cosetFamily A) i
      simpa only [← hga, mul_smul, inv_smul_smul] using hxa
    have hright : x∈Universal.cosetFamily A (!i) := by
      rw [← stabilizer_base (Universal.cosetFamily A)]
      change x • base (Universal.cosetFamily A) (!i)=base (Universal.cosetFamily A) (!i)
      apply (MulAction.toPerm g).injective
      change g • (x • base (Universal.cosetFamily A) (!i))=g • base (Universal.cosetFamily A) (!i)
      simpa only [← hgb, mul_smul, inv_smul_smul] using hxb
    rw [originalMiddle, ← Universal.overlap_eq A hL hR]
    cases i
    · exact ⟨hleft, hright⟩
    · exact ⟨hright, hleft⟩
  have hKF : cartan c ≤ F := by
    intro k hk j _
    have hkg : g*k*g⁻¹∈cartan c :=
      (Subgroup.mem_normalizer_iff.mp (hnormalizes hg) k).mp hk
    exact reflectionApartment_fixed c t htnorm _ hkg _ (hT _ (p.getVert_mem_support j))
  have hf := intermediate_factorization c h F hFB hKF
  have hmap : F.map e=pathFixer (X := A.Universal) p :=
    Subgroup.map_comap_eq_self_of_surjective (MulAut.conj g).surjective _
  have hrootmap : (F.pCoreIn 2).map e=pathRoot (X := A.Universal) p := by
    rw [Subgroup.map_pCoreIn_of_injective 2 F e (MulAut.conj g).injective, hmap]
    rfl
  have hKmap : (cartan c).map e=cartan c :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormalizes hg)
  ext x
  constructor
  · intro hx
    have hx' : x∈F.map e := hmap.symm ▸ hx
    obtain ⟨z, hz, rfl⟩ := hx'
    change z∈(F : Set A.Universal) at hz
    rw [hf] at hz
    obtain ⟨u, hu, k, hk, rfl⟩ := hz
    refine ⟨e u, ?_, e k, ?_, (map_mul e u k).symm⟩
    · rw [← hrootmap]
      exact ⟨u, hu, rfl⟩
    · rw [← hKmap]
      exact ⟨k, hk, rfl⟩
  · rintro ⟨u, hu, k, hk, rfl⟩
    exact (pathFixer p).mul_mem (Subgroup.pCoreIn_le 2 _ hu)
      (fun j _ => reflectionApartment_fixed c t htnorm k hk _ (hT _ (p.getVert_mem_support j)))


end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
