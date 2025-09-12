ensure_path('TEXINPUTS', '~/repo/HOL/src/TeX');

add_cus_dep('hix', 'tid', 0, 'munge');
add_cus_dep('hix', 'tde', 0, 'munge');

sub munge {
  return system("./munge.exe -index \"$_[0]\"" );
}

push @generated_exts, 'hix', 'tid', 'tde'
