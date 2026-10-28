module

public import Theory.SpecificGroups.Lyons.GebhardtMatrixWords
public import Theory.SpecificGroups.Lyons.GebhardtMatrixCertificateData
public import Theory.SpecificGroups.Lyons.GebhardtMatrixCertificateStrings

/-!
# Independent obligations for the Gebhardt matrix certificate

The five generator words and the finite relation checks share ten fixed signed
matrices. An image certificate connects the words and their inverses to these
matrices. A product certificate checks the 25 signed relator strings and the
two ambient recovery strings. The bridge below combines both certificates into
the original `WordCertificate`, without any group-order or recognition premise.

Source: Gebhardt, Experimental Mathematics 9 (2000), 333-338, Section 3B;
`GebhardtMatrixSource/` documents the discovered words and original matrices.
-/

namespace Lyons.Gebhardt.MatrixRealization.CertificateInputs

/-- Read a signed source letter as its explicit candidate matrix. -/
@[expose] public def matrixLetter : Char → AtlasMatrix
  | 'a' => candidateMatrix 0 false | 'A' => candidateMatrix 0 true
  | 'b' => candidateMatrix 1 false | 'B' => candidateMatrix 1 true
  | 'c' => candidateMatrix 2 false | 'C' => candidateMatrix 2 true
  | 'd' => candidateMatrix 3 false | 'D' => candidateMatrix 3 true
  | 'z' => candidateMatrix 4 false | 'Z' => candidateMatrix 4 true
  | _ => 1

/-- Ordinary left-to-right multiplication of signed candidate matrices. -/
@[expose] public def matrixWord (s : String) : AtlasMatrix :=
  (s.toList.map matrixLetter).prod

/-- Both signed images of one of the five explicit words. -/
public structure GeneratorImageCertificate (i : Alphabet) : Prop where
  positive : matrixRepresentation (wordData.assignment i) = candidateMatrix i false
  negative : matrixRepresentation ((wordData.assignment i)⁻¹) = candidateMatrix i true

/-- The word images agree with all ten fixed signed matrices. -/
public abbrev ImageCertificate := ∀ i : Alphabet, GeneratorImageCertificate i

/-- A certified right inverse supplies the negative image once the positive
word image is known. Only one inverse product needs to be checked. -/
public theorem generatorImageCertificate_of_positive (i : Alphabet)
    (hp : matrixRepresentation (wordData.assignment i) = candidateMatrix i false)
    (hm : candidateMatrix i false * candidateMatrix i true = 1) :
    GeneratorImageCertificate i where
  positive := hp
  negative := by
    calc
      matrixRepresentation ((wordData.assignment i)⁻¹) =
          matrixRepresentation ((wordData.assignment i)⁻¹) * 1 := (mul_one _).symm
      _ = matrixRepresentation ((wordData.assignment i)⁻¹) *
          (candidateMatrix i false * candidateMatrix i true) := by rw [hm]
      _ = (matrixRepresentation ((wordData.assignment i)⁻¹) *
          matrixRepresentation (wordData.assignment i)) * candidateMatrix i true := by
        rw [hp, mul_assoc]
      _ = candidateMatrix i true := by
        rw [← map_mul, inv_mul_cancel, map_one, one_mul]

/-- Assemble the four local image checks and the independent outer image check. -/
public theorem imageCertificate_of_local_outer
    (hl : ∀ i : Alphabet, i.val < 4 → GeneratorImageCertificate i)
    (hz : GeneratorImageCertificate 4) : ImageCertificate := by
  intro i
  by_cases hi : i.val < 4
  · exact hl i hi
  · have he : i = 4 := by
      apply Fin.ext
      change i.val = 4
      omega
    simpa only [he] using hz

/-- The independent finite products needed after the word images are certified. -/
public structure ProductCertificate : Prop where
  relations : ∀ s ∈ relatorStrings, matrixWord s = 1
  recoverA : matrixWord "ccacDCAbbDCCaCdaCCaCACBcACabbcBacAzdBzcbCDZbCA" = atlasAMatrix
  recoverB : matrixWord "BCAcabcAcacBBabaBABDCACAbABDaaCACAccDCBDCBzbbdcbCZdCbCZA" = atlasBMatrix

private theorem letter_image (h : ImageCertificate) (c : Char) :
    matrixRepresentation (FreeGroup.lift wordData.assignment (letter c)) = matrixLetter c := by
  unfold letter
  split <;>
    simp_all only [matrixLetter, FreeGroup.lift_apply_of, map_inv, map_one,
      (h 0).positive, (h 0).negative, (h 1).positive, (h 1).negative,
      (h 2).positive, (h 2).negative, (h 3).positive, (h 3).negative,
      (h 4).positive, (h 4).negative]

/-- Evaluation of a signed string agrees with its ordinary matrix product. -/
public theorem word_image (h : ImageCertificate) (s : String) :
    matrixRepresentation (FreeGroup.lift wordData.assignment (word s)) = matrixWord s := by
  simp only [word, matrixWord, map_list_prod, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro c _
  exact letter_image h c

/-- Assemble independent image and product certificates for the concrete words. -/
public theorem wordCertificate_of_images_products
    (hi : ImageCertificate) (hp : ProductCertificate) : WordCertificate wordData where
  relations := by
    intro r hr
    change r ∈ parabolicRelators ++ localRelators ++ outerRelators at hr
    rw [← relatorStrings_eq] at hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact (word_image hi s).trans (hp.relations s hs)
  recoverA := (word_image hi _).trans hp.recoverA
  recoverB := (word_image hi _).trans hp.recoverB

end Lyons.Gebhardt.MatrixRealization.CertificateInputs
