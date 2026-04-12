#[ macro_export ]
macro_rules! define_template {
    () => {
        #[ derive (askama::Template) ]
        #[ template (path = "empty.txt") ]
        struct Empty {}
    }
}
